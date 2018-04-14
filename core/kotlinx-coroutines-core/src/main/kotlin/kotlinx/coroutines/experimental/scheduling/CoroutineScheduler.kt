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
// todo: Take maxPoolSize from system property.
// todo: Base default maxPoolSize on a `noOfCPUs * someFactor` so that it scales.
// todo: On "larger" workstations maxPoolSize should be correspondingly larger ("small machine" will run out of memory)
class CoroutineScheduler(private val corePoolSize: Int, private val maxPoolSize: Int = 16384) : Closeable {

    private val globalWorkQueue: GlobalQueue = ConcurrentLinkedQueue<Task>()

    /*
     * Permits to execute non-blocking (~CPU-intensive) tasks.
     * If worker owns a permit, it can schedule non-blocking tasks to its queue and steal work from other workers.
     * If worker doesn't, it can execute only blocking tasks (and non-blocking leftovers from its local queue)
     * and will try to park as soon as its queue is empty.
     */
    private val cpuPermits = Semaphore(corePoolSize, false)

    // todo: Consider putting retired workers into stack as opposed to queue.
    // todo: Next time we need a worker we'll get the "warmest" one
    // todo: Take a look at ObjectPool implementation from kotlinx.io module (it is lock-free & zero-garbage stack)
    // todo: However, since all workers are already numbered (indexed) and have PoolWorker objects, you can have a very simply impl
    // todo: Just implement Treiber stack using `val nextRetiredIndexVersion = atomic(0)` in each PoolWorker and keep top here
    private val retiredWorkers = ConcurrentLinkedQueue<PoolWorker>()

    /**
     * State of worker threads
     * [workers] is array of lazily created workers up to [maxPoolSize] workers
     * [createdWorkers] is count of already created workers (worker with index lesser than [createdWorkers] exists)
     * [blockingWorkers] is count of running workers which are executing [TaskMode.PROBABLY_BLOCKING] task
     */
    private val workers: Array<PoolWorker?>
    private val createdWorkers = atomic(0)
    // todo: We should keep track of cpuWorkers. See comment in `requestCpuWorker`
    private val blockingWorkers = atomic(0)
    private val random = Random()

    // todo: It should be atomic. See comment in `close`
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
        // todo: can we lazily create corePool, too?
        // todo: The goal: when running "small" workload on "large" machine we should not consume extra resource in advance
        // todo: Can't we just invoke createNewWorker here to get the first one up and running?
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
        // todo: isTerminated should be atomic with `if (!isTerminated.compareAndSet(0, 1)) return` here
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
        // todo: This is an extra allocation of TimedTask on dispatch that we can avoid.
        // todo: Turn TimedTask into an interface with settable time and mode, make DispatchedTask extend TimedTask,
        // todo: Implement it in all concrete classes implementing DispatchedTask.
        // todo: Note, that an instance of DispatchedTask is cached (reused) per state machine.
        val task = TimedTask(block, schedulerTimeSource.nanoTime(), mode)

        // todo: Idiomatic Kotlin: use `when (submitToLocalQueue(task, fair))` here
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
         * Fast path -- we have retired worker, unpark it, and we're done.
         * The benign data race here: when only one permit is available, multiple retired workers
         * can be unparked, but only one will continue execution
         */
        val retired = retiredWorkers.poll()
        if (retired != null) {
            LockSupport.unpark(retired)
            return
        }

        // todo: Here we are reading two atomic counters separately and computing difference
        // todo: Observe, that we never use the value of blockingWorkers itself.
        // todo: Only cpuWorkers = created - blocking is important and used
        // todo: We should maintain cpuWorkersCounter instead of blockingWorkers
        // todo: Don't forget to increment cpuWorkersCounter in createNewWorker
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
        // todo: Use createdWorkers.loop { nextWorker -> ... } idiom here.
        // todo: It makes it explicit that we doing lock-free loop on createdWorkers atomic.
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
            // todo: Here we have a similar problem to trySteal, with different types of threads
            // todo: When we have a large number of active (non-parked) worker threads, then it is hard to find one
            // todo: If we have lots of blocking threads busy doing some IO (they are not parking and not retired),
            // todo: then it is even harder to find a parked one among them.
            // todo: Since we care to unpark _any_ parked one, do we really need random here?
            // todo: We can just maintain a stack of all parked workers.
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

        // todo: Micro-optimization: pass task.mode as parameter to this fun, avoid reading it from property
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

        val addResult = if (fair) {
            worker.localQueue.addLast(task, globalWorkQueue)
        } else {
            worker.localQueue.add(task, globalWorkQueue)
        }
        if (addResult) {
            // We're close to queue capacity, wake up anyone to steal work
            // Note: non-atomic bufferSize here is Ok (it is just a performance optimization)
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

    // todo: make name of the pool configurable (optional parameter to CoroutineScheduler) and base thread names on it
    internal inner class PoolWorker(val index: Int) : Thread("CoroutineScheduler-worker-$index") {
        init {
            isDaemon = true
        }

        val localQueue: WorkQueue = WorkQueue()

        // todo: hasCpuPermit + isBlocking is actaully a single state variable with 3 possible states (not four!)
        // todo: Notice: cannot hasCpuPermit && isBlocking at the same time.
        // todo: Merging them would simplify code and make worker state changes atomic to the external observers.
        @Volatile
        var hasCpuPermit = false
        var isBlocking = false

        /**
         * Time of the last call to [requestCpuWorker] due to missing tasks deadlines.
         * Used as throttling mechanism to avoid unparking multiple threads when it's not necessary
         */
        private var lastExhaustionTime = 0L

        // todo: Same story here. Merge hasCpuPermit + isBlocking + isParking it a single state work.
        // todo: Notice: Cannot hasCpuPermit && isParking
        @Volatile
        var isParking = false

        // todo: It does not seem that @Volatile is of any value here.
        // todo: It is incremented between calls to findTask which _already_ has globalWorkQueue.poll()
        @Volatile
        private var spins = 0L
        // todo: Given the above consideration with can combine spins & yields into a single var
        // todo: Micro-optimization: A single combined spins+yields counter will make `idleReset` slightly faster
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
            // todo: consider dropping output of bound value & generating another one (until in bounds)
            // todo: reminder operation is very, very slow (can be slower than generating another random with xor/shift)
            // todo: needs benchmark
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
                    // todo: just isParking = true is all we need here (no need for `if`)
                    // todo: it _is_ a volatile write, but it should be still cheaper that using `if`
                    if (!isParking) {
                        isParking = true
                    }

                    if (parkTimeNs < MAX_PARK_TIME_NS) {
                        // todo: `x * 3 shr 1` is better than `x * 1.5` for performance-optimized code
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

        // todo: The current logic here is to always take globalWorkQueue if there is some work
        // todo: If incoming rate is too fast, this can lead to starvation of non-empty localQueues in threads with CPU permits
        // todo: Moreover, on overflow of local queues they post to globalQueue, thus aggravating starvation
        // todo: It looks like the simplest strategy is to alternate between global-first / local-first to load-balance
        private fun findTask(): Task? {
            // todo: we we are reading volatile hasCpuPermit too often here.
            // todo: for performance, it should be load once into local val hasCpuPermit, then used
            hasCpuPermit = hasCpuPermit || cpuPermits.tryAcquire()

            var task: Task?
            if (hasCpuPermit) {
                // :todo: Idiomatic Kotlin does not need var: globalWorkQueue.poll()?.let { return it }
                task = globalWorkQueue.poll()
                if (task != null) return task
            }

            // :todo: Idiomatic Kotlin does not need var: localQueue.poll()?.let { return it }
            task = localQueue.poll()
            if (task != null) return task

            // todo: Idiomatic Kotlin: return if (hasCpuPermit) trySteal() else null
            if (hasCpuPermit) {
                return trySteal()
            }

            return null
        }

        private fun trySteal(): Task? {
            // 0 to await an initialization and 1 to avoid excess stealing on single-core machines
            // todo: should not read createdWorkers.value twice.
            // todo: Read it once when trying to find a worker to steal from.
            if (createdWorkers.value < 2) {
                return null
            }

            // Probe a couple of workers
            // TODO coarse grained mechanism when used with blocking dispatcher
            // todo: Do we really need STEAL_ATTEMPTS > 1 ???
            // todo: If steal fails and returns null we quickly spin again into trySteal.
            repeat(STEAL_ATTEMPTS) {
                // todo: We are wasting time here tyring to steal from all workers ever created.
                // todo: It is inefficient when there are many retired workers.
                // todo: We need to find a solution that does not degrade over time.
                val worker = workers[nextInt(createdWorkers.value)]
                if (worker !== null && worker !== this) {
                    if (localQueue.trySteal(worker.localQueue, globalWorkQueue)) {
                        return@repeat
                    }
                }
            }
            // todo: why not just return null here and let it retry in top-level loop?
            return localQueue.poll()
        }
    }
}
