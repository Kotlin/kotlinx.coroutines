package kotlinx.coroutines.experimental.scheduling

import kotlinx.atomicfu.atomic
import kotlinx.coroutines.experimental.Runnable
import java.io.Closeable
import java.util.*
import java.util.concurrent.ConcurrentLinkedQueue
import java.util.concurrent.Semaphore
import java.util.concurrent.TimeUnit
import java.util.concurrent.locks.LockSupport

/**
 * Coroutine scheduler (pool of shared threads) which primary target is to distribute dispatched coroutine over worker threads,
 * including both CPU-intensive and blocking tasks.
 *
 * Current scheduler implementation has two optimization targets:
 * 1) Efficiency in the face of communication patterns (e.g., actors communicating via channel)
 * 2) Dynamic resizing to support blocking calls without re-dispatching coroutine to separate "blocking" thread pool
 *
 * Structural overview
 * Scheduler consists of [corePoolSize] worker threads to execute CPU-bound tasks and up to [maxPoolSize] (lazily created) threads
 * to execute blocking tasks. Every worker has local queue in addition to global scheduler queue and global queue
 * has priority over local queue to avoid starvation of externally-submitted (e.g., from Android UI thread) tasks and work-stealing is implemented
 * on top of that queues to provide even load distribution and illusion of centralized run queue.
 *
 * Scheduling
 * When a coroutine is dispatched from within scheduler worker, it's placed into the head of worker run queue.
 * If the head is not empty, the task from the head is moved to the tail. Though it is unfair scheduling policy,
 * it couples communicating coroutines into one and eliminates scheduling latency that arises from placing task in the end of the queue.
 * Placing former head to the tail is necessary to provide semi-FIFO order, otherwise queue degenerate to stack.
 * When a coroutine is dispatched from an external thread, it's put into the global queue.
 *
 * Work stealing and affinity
 * To provide even tasks distribution worker tries to steal tasks from other workers queues before parking when his local queue is empty.
 * A non-standard solution is implemented to provide tasks affinity: task may be stolen only if it's 'stale' enough (based on the value of [WORK_STEALING_TIME_RESOLUTION_NS]).
 * For this purpose monotonic global clock ([System.nanoTime]) is used and every task has associated with it submission time.
 * This approach shows outstanding results when coroutines are cooperative, but as downside scheduler now depends on high-resolution global clock
 * which may limit scalability on NUMA machines.
 *
 * Dynamic resizing and support of blocking tasks
 * To support possibly blocking tasks [TaskMode] and CPU quota (via [cpuPermits]) are used.
 * To execute [TaskMode.NON_BLOCKING] tasks from the global queue or to steal tasks from other workers
 * the worker should have CPU permit. When a worker starts executing [TaskMode.PROBABLY_BLOCKING] task,
 * it releases its CPU permit, giving a hint to a scheduler that additional thread should be created (or awaken)
 * if new [TaskMode.NON_BLOCKING] task will arrive. When a worker finishes executing blocking task, it executes
 * all tasks from its local queue (including [TaskMode.NON_BLOCKING]) and then parks as retired without polling
 * global queue or trying to steal new tasks. Such approach may slightly limit scalability (allowing more than [corePoolSize] threads
 * to execute CPU-bound tasks at once), but in practice, it is not, significantly reducing context switches and tasks re-dispatching.
 *
 * Note: will be internal after integration with Ktor
 */
class CoroutineScheduler(private val corePoolSize: Int, private val maxPoolSize: Int = 16384) : Closeable {

    private val globalWorkQueue: GlobalQueue = ConcurrentLinkedQueue<Task>()

    /*
     * Permits to execute non-blocking (~CPU-intensive) tasks.
     * If worker owns a permit, it can schedule non-blocking tasks to its queue and steal work from other workers.
     * If worker doesn't, it can execute only blocking tasks (and non-blocking leftovers from its local queue)
     * and will try to park as soon as his queue will be empty.
     */
    private val cpuPermits = Semaphore(corePoolSize, false)
    private val retiredWorkers = ConcurrentLinkedQueue<PoolWorker>()

    /**
     * State of worker threads
     * [workers] is array of lazily created workers up to [maxPoolSize] workers
     * [createdWorkers] is count of already created workers (worker with index lesser than [createdWorkers] exists)
     * [blockingWorkers] is count of running workers which are executing [TaskMode.PROBABLY_BLOCKING] task
     */
    private val workers: Array<PoolWorker?>
    private val createdWorkers = atomic(0)
    private val blockingWorkers = atomic(0)
    private val random = Random()

    @Volatile
    private var isTerminated = false

    companion object {
        private const val STEAL_ATTEMPTS = 4
        private const val MAX_SPINS = 1000L
        private const val MAX_YIELDS = 500L
        @JvmStatic
        private val MAX_PARK_TIME_NS = TimeUnit.SECONDS.toNanos(1)
        @JvmStatic
        private val MIN_PARK_TIME_NS = (WORK_STEALING_TIME_RESOLUTION_NS / 4).coerceAtLeast(10).coerceAtMost(MAX_PARK_TIME_NS)

        // Local queue 'add' results
        private const val ADDED = -1
        private const val ADDED_REQUIRES_HELP = 0 // Added to the local queue, but pool requires additional worker to keep up
        private const val NOT_ADDED = 1
    }

    init {
        require(corePoolSize >= 1, { "Expected positive core pool size, but was $corePoolSize" })
        require(maxPoolSize >= corePoolSize, { "Expected max pool size ($maxPoolSize) greater than or equals to core pool size ($corePoolSize)" })
        workers = arrayOfNulls(maxPoolSize)
        for (i in 0 until corePoolSize) {
            workers[i] = PoolWorker(i).apply { start() }
        }

        createdWorkers.value = corePoolSize
    }

    /*
     * Closes current scheduler and waits until all threads will be stopped.
     * This method uses unsafe API (unconditional unparks, ignoring interruptions etc.)
     * and intended to be used only for testing. Invocation has no additional effect if already closed.
     */
    override fun close() {
        if (isTerminated) {
            return
        }

        isTerminated = true

        // Race with recently created threads which may park indefinitely
        var finishedThreads = 0
        while (finishedThreads != createdWorkers.value) {
            var finished = 0
            for (i in 0 until createdWorkers.value) {
                workers[i]?.also {
                    if (it.isAlive) {
                        // Unparking alive thread is unsafe in general, but acceptable for testing purposes
                        LockSupport.unpark(it)
                        it.join(1_000)
                    }

                    ++finished
                }
            }

            finishedThreads = finished
        }
    }

    /**
     * Dispatches execution of a runnable [block] with a hint to a scheduler whether
     * this [block] may execute blocking operations (IO, system calls, locking primitives etc.)
     *
     * @param block runnable to be dispatched
     * @param mode mode of given [block] which is used as a hint to a dynamic resizing mechanism
     * @param fair whether the task should be dispatched fairly (strict FIFO) or not (semi-FIFO)
     */
    fun dispatch(block: Runnable, mode: TaskMode = TaskMode.NON_BLOCKING, fair: Boolean = false) {
        val task = TimedTask(block, schedulerTimeSource.nanoTime(), mode)

        val offerResult = submitToLocalQueue(task, fair)
        if (offerResult == ADDED) {
            return
        }

        if (offerResult == NOT_ADDED) {
            globalWorkQueue.add(task)
        }

        // Unpark anyone, if the task was added to the global queue or local is close to overflow
        requestCpuWorker()
    }

    /**
     * Unparks or creates a new [PoolWorker] for executing non-blocking tasks if there are idle cores
     */
    private fun requestCpuWorker() {
        // All cores are already busy with CPU work
        if (cpuPermits.availablePermits() == 0) {
            return
        }

        /*
         * Fast path -- we have retired worker, unpark him, and we're done.
         * The benign data race here: when only one permit is available, multiple retired workers
         * can be unparked, but only one will continue execution
         */
        val retired = retiredWorkers.poll()
        if (retired != null) {
            LockSupport.unpark(retired)
            return
        }

        val created = createdWorkers.value
        val blocking = blockingWorkers.value
        val cpuWorkers = created - blocking
        // If most of created workers are blocking, we should create one more thread to handle non-blocking work
        if (cpuWorkers < corePoolSize) {
            createNewWorker()
            return
        }

        unparkAny()
    }

    private fun createNewWorker() {
        while (true) {
            val nextWorker = createdWorkers.value
            // Limit is reached, bail out
            if (nextWorker >= maxPoolSize || cpuPermits.availablePermits() == 0) {
                return
            }

            if (createdWorkers.compareAndSet(nextWorker, nextWorker + 1)) {
                require(workers[nextWorker] == null)
                val worker = PoolWorker(nextWorker).apply { start() }
                workers[nextWorker] = worker
                return
            }
        }
    }

    private fun unparkAny() {
        // Probabilistically try to unpark someone
        repeat(STEAL_ATTEMPTS) {
            val victim = workers[random.nextInt(createdWorkers.value)]
            if (victim != null && victim.isParking) {
                /*
                 * The benign data race, the victim can wake up after this check, but before 'unpark' call succeeds,
                 * making first 'park' in next idle period a no-op
                 */
                LockSupport.unpark(victim)
                return
            }
        }
    }

    private fun submitToLocalQueue(task: Task, fair: Boolean): Int {
        val worker = Thread.currentThread() as? PoolWorker ?: return NOT_ADDED
        var result = ADDED

        if (task.mode == TaskMode.NON_BLOCKING) {
            /*
             * If the worker is currently executing blocking task and tries to dispatch non-blocking task, it's one the following reasons:
             * 1) Blocking worker is finishing its block and resumes non-blocking continuation
             * 2) Blocking worker starts to create non-blocking jobs
             *
             * First use-case is expected (as recommended way of using blocking contexts),
             * so we add non-blocking task to local queue, but also request CPU worker to mitigate second case
             */
            if (worker.isBlocking) {
                result = ADDED_REQUIRES_HELP
            } else {
                /*
                 * If thread is not blocking, then it's just tries to finish its
                 * local work in order to park (or grab another blocking task), do not add non-blocking tasks
                 * to its local queue
                 */
                worker.hasCpuPermit = worker.hasCpuPermit || cpuPermits.tryAcquire()
                if (!worker.hasCpuPermit) {
                    return NOT_ADDED
                }
            }
        }

        val addResult = if (fair) worker.localQueue.addLast(task, globalWorkQueue) else worker.localQueue.add(task, globalWorkQueue)
        if (addResult) {
            // We're close to queue capacity, wake up anyone to steal work
            if (worker.localQueue.bufferSize > QUEUE_SIZE_OFFLOAD_THRESHOLD) {
                return ADDED_REQUIRES_HELP
            }

            return result
        }

        return ADDED_REQUIRES_HELP
    }

    /**
     * Returns a string identifying the state of this scheduler for nicer debugging.
     * Note that this method is not atomic and represents rough state of pool.
     *
     * State of the queues:
     * b for blocking, c for CPU, r for retiring.
     * E.g. for [1b, 1b, 2c, 1r] means that pool has
     * two blocking workers with queue size 1, one worker with CPU permit and queue size 1
     * and one retiring (executing his local queue before parking) worker with queue size 1.
     */
    override fun toString(): String {
        var parkedWorkers = 0
        var blockingWorkers = 0
        var cpuWorkers = 0

        val queueSizes = arrayListOf<String>()
        for (worker in workers) {
            if (worker == null) {
                continue
            }

            val queueSize = worker.localQueue.size()
            when {
                worker.isParking -> ++parkedWorkers
                worker.isBlocking -> {
                    ++blockingWorkers
                    queueSizes += queueSize.toString() + "b" // Blocking
                }
                worker.hasCpuPermit -> {
                    ++cpuWorkers
                    queueSizes += queueSize.toString() + "c" // CPU
                }
                queueSize > 0 -> {
                    queueSizes += queueSize.toString() + "r" // Retiring
                }
            }

        }

        return "${super.toString()}[core pool size = ${workers.size}, " +
                "CPU workers = $cpuWorkers, " +
                "blocking workers = $blockingWorkers, " +
                "parked workers = $parkedWorkers, " +
                "retired workers = ${retiredWorkers.size}, " +
                "running workers queues = $queueSizes, " +
                "global queue size = ${globalWorkQueue.size}]"
    }

    internal inner class PoolWorker(val index: Int) : Thread("CoroutineScheduler-worker-$index") {
        init {
            isDaemon = true
        }

        val localQueue: WorkQueue = WorkQueue()
        @Volatile
        var hasCpuPermit = false
        var isBlocking = false

        /**
         * Time of the last call to [requestCpuWorker] due to missing tasks deadlines.
         * Used as throttling mechanism to avoid unparking multiple threads when it's not necessary
         */
        private var lastExhaustionTime = 0L

        @Volatile
        var isParking = false
        @Volatile
        private var spins = 0L
        private var yields = 0L
        private var parkTimeNs = MIN_PARK_TIME_NS
        private var rngState = random.nextInt()

        override fun run() {
            while (!isTerminated) {
                val job = findTask()
                if (job == null) {
                    // Wait for a job with potential park
                    idle()
                } else {
                    idleReset()
                    beforeTask(job)
                    runSafely(job.task)
                    afterTask(job)
                }
            }

            if (hasCpuPermit) {
                hasCpuPermit = false
                cpuPermits.release()
            }
        }

        private fun runSafely(block: Runnable) {
            try {
                block.run()
            } catch (t: Throwable) {
                uncaughtExceptionHandler.uncaughtException(this, t)
            }
        }

        private fun beforeTask(job: Task) {
            if (job.mode != TaskMode.NON_BLOCKING) {
                isBlocking = true
                /*
                 * We should increment blocking workers *before* checking CPU starvation,
                 * otherwise requestCpuWorker() will not count current thread as starving
                 */
                blockingWorkers.incrementAndGet()
                if (hasCpuPermit) {
                    hasCpuPermit = false
                    cpuPermits.release()
                    requestCpuWorker()
                }

                return
            }

            /*
             * If we have idle CPU and the current worker is exhausted, wake up one more worker.
             * Check last exhaustion time to avoid the race between steal and next task execution
             */
            if (cpuPermits.availablePermits() == 0) {
                return
            }

            val now = schedulerTimeSource.nanoTime()
            if (now - job.submissionTime >= WORK_STEALING_TIME_RESOLUTION_NS && now - lastExhaustionTime >= WORK_STEALING_TIME_RESOLUTION_NS * 5) {
                lastExhaustionTime = now
                requestCpuWorker()
            }
        }


        private fun afterTask(job: Task) {
            if (job.mode != TaskMode.NON_BLOCKING) {
                blockingWorkers.decrementAndGet()
                isBlocking = false
            }
        }

        /*
         * Marsaglia xorshift RNG with period 2^32-1 for work stealing purposes.
         * ThreadLocalRandom cannot be used to support Android and ThreadLocal<Random> is up to 15% slower on Ktor benchmarks
         */
        internal fun nextInt(upperBound: Int): Int {
            rngState = rngState xor (rngState shl 13)
            rngState = rngState xor (rngState shr 17)
            rngState = rngState xor (rngState shl 5)
            val mask = upperBound - 1
            // Fast path for power of two bound
            if (mask and upperBound == 0) {
                return rngState and mask
            }

            return (rngState and Int.MAX_VALUE) % upperBound
        }

        private fun idle() {
            // at some point all is disabled
            if (hasCpuPermit) {
                cpuWorkerIdle()
            } else {
                blockingWorkerIdle()
            }
        }

        private fun cpuWorkerIdle() {
            /*
             * Simple adaptive await of work:
             * Spin on the volatile field with an empty loop in hope that new work will arrive,
             * then start yielding to reduce CPU pressure, and finally start adaptive parking.
             *
             * The main idea is not to park while it's possible (otherwise throughput on asymmetric workloads suffers due to too frequent
             * park/unpark calls and delays between job submission and thread queue checking)
             */
            when {
                spins < MAX_SPINS -> ++spins
                ++yields <= MAX_YIELDS -> yield()
                else -> {
                    if (!isParking) {
                        isParking = true
                    }

                    if (parkTimeNs < MAX_PARK_TIME_NS) {
                        parkTimeNs = (parkTimeNs * 1.5).toLong().coerceAtMost(MAX_PARK_TIME_NS)
                    }

                    if (hasCpuPermit) {
                        hasCpuPermit = false
                        cpuPermits.release()
                    }
                    LockSupport.parkNanos(parkTimeNs)
                }
            }
        }

        private fun blockingWorkerIdle() {
            isParking = true
            retiredWorkers.add(this)
            LockSupport.parkNanos(Long.MAX_VALUE)
        }

        private fun idleReset() {
            if (isParking) {
                isParking = false
                parkTimeNs = MIN_PARK_TIME_NS
            }

            spins = 0
            yields = 0
        }

        private fun findTask(): Task? {
            hasCpuPermit = hasCpuPermit || cpuPermits.tryAcquire()

            var task: Task?
            if (hasCpuPermit) {
                task = globalWorkQueue.poll()
                if (task != null) return task
            }

            task = localQueue.poll()
            if (task != null) return task

            if (hasCpuPermit) {
                return trySteal()
            }

            return null
        }

        private fun trySteal(): Task? {
            // 0 to await an initialization and 1 to avoid excess stealing on single-core machines
            if (createdWorkers.value < 2) {
                return null
            }

            // Probe a couple of workers
            // TODO coarse grained mechanism when used with blocking dispatcher
            repeat(STEAL_ATTEMPTS) {
                val worker = workers[nextInt(createdWorkers.value)]
                if (worker !== null && worker !== this) {
                    if (localQueue.trySteal(worker.localQueue, globalWorkQueue)) {
                        return@repeat
                    }
                }
            }

            return localQueue.poll()
        }
    }
}
