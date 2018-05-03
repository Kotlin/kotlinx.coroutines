package kotlinx.coroutines.experimental.scheduling

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.*
import java.io.*
import java.util.*
import java.util.concurrent.*
import java.util.concurrent.locks.*

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
 * Placing former head to the tail is necessary to provide semi-FIFO order, otherwise queue degenerates to stack.
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
 */
@Suppress("NOTHING_TO_INLINE")
internal class CoroutineScheduler(
    private val corePoolSize: Int,
    private val maxPoolSize: Int = corePoolSize * 128
) : Closeable {

    private val globalWorkQueue: LockFreeQueue = LockFreeQueue()

    /*
     * Permits to execute non-blocking (~CPU-intensive) tasks.
     * If worker owns a permit, it can schedule non-blocking tasks to its queue and steal work from other workers.
     * If worker doesn't, it can execute only blocking tasks (and non-blocking leftovers from its local queue)
     * and will try to park as soon as its queue is empty.
     */
    private val cpuPermits = Semaphore(corePoolSize, false)

    /*
     * The stack of parker workers (with an artificial object to make call-sites more understandable).
     * Every worker registers itself in a stack before parking (if it was not previously registered)
     * and callers of [requestCpuWorker] will try to unpark a thread from the top of a stack.
     * This is a form of intrusive garbage-free Treiber stack where PoolWorker also is a stack node.
     *
     * The stack is better than a queue (even with contention on top) because it unparks threads
     * in most-recently used order, improving both performance and locality.
     * Moreover, it decreases threads thrashing, if the pool has n threads when only n / 2 is required,
     * the latter half will never be unparked and will terminate itself after [BLOCKING_WORKER_KEEP_ALIVE_NS].
     */
    @Suppress("ClassName")
    private object parkedWorkersStack
    private val head = atomic<PoolWorker?>(null)

    @Suppress("unused")
    private fun parkedWorkersStack.push(next: PoolWorker) {
        head.loop { h ->
            next.nextParkedWorker = h
            if (head.compareAndSet(h, next)) return
        }
    }

    @Suppress("unused")
    private fun parkedWorkersStack.pop(): PoolWorker? {
        // TODO investigate ABA possibility
        head.loop { h ->
            if (h == null) return null
            val next = h.nextParkedWorker
            if (head.compareAndSet(h, next)) {
                h.nextParkedWorker = null
                return h
            }
        }
    }

    /**
     * State of worker threads
     * [workers] is array of lazily created workers up to [maxPoolSize] workers
     * [createdWorkers] is count of already created workers (worker with index lesser than [createdWorkers] exists)
     * [blockingWorkers] is count of running workers which are executing [TaskMode.PROBABLY_BLOCKING] task
     */
    private val workers: Array<PoolWorker?>

    /*
     * Long describing state of workers in this pool.
     * Currently includes created and blocking workers
     */
    private val controlState = atomic(0L)
    private val createdWorkers: Int inline get() = (controlState.value and CREATED_MASK).toInt()
    private val blockingWorkers: Int inline get() = (controlState.value and BLOCKING_MASK shr 21).toInt()

    private inline fun createdWorkers(state: Long): Int = (state and CREATED_MASK).toInt()
    private inline fun blockingWorkers(state: Long): Int = (state and BLOCKING_MASK shr 21).toInt()

    private inline fun incrementCreatedWorkers(): Int = createdWorkers(controlState.addAndGet(1L))
    private inline fun decrementCreatedWorkers(): Int = createdWorkers(controlState.addAndGet(-1L))
    private inline fun incrementBlockingWorkers(): Int = blockingWorkers(controlState.addAndGet(1L shl 21))
    private inline fun decrementBlockingWorkers(): Int = blockingWorkers(controlState.addAndGet(-(1L shl 21)))

    private val random = Random()
    private val isTerminated = atomic(false)

    companion object {
        private const val MAX_SPINS = 1000L
        private const val MAX_YIELDS = 500L

        @JvmStatic
        private val MAX_PARK_TIME_NS = TimeUnit.SECONDS.toNanos(1)

        @JvmStatic
        private val MIN_PARK_TIME_NS = (WORK_STEALING_TIME_RESOLUTION_NS / 4)
            .coerceAtLeast(10)
            .coerceAtMost(MAX_PARK_TIME_NS)

        @JvmStatic
        private val BLOCKING_WORKER_KEEP_ALIVE_NS = TimeUnit.SECONDS.toNanos(5)

        // Local queue 'add' results
        private const val ADDED = -1
        // Added to the local queue, but pool requires additional worker to keep up
        private const val ADDED_REQUIRES_HELP = 0
        private const val NOT_ADDED = 1

        // Worker termination states
        private const val FORBIDDEN = -1
        private const val ALLOWED = 0
        private const val TERMINATED = 1

        // Masks of control state
        private const val CREATED_MASK: Long = (1L shl 21) - 1
        private const val BLOCKING_MASK: Long = CREATED_MASK shl 21
    }

    init {
        require(corePoolSize >= 1) {
            "Expected positive core pool size, but was $corePoolSize"
        }
        require(maxPoolSize >= corePoolSize) {
            "Expected max pool size ($maxPoolSize) greater than or equals to core pool size ($corePoolSize)"
        }

        workers = arrayOfNulls(maxPoolSize)
        // todo: can we lazily create corePool, too?
        // todo: The goal: when running "small" workload on "large" machine we should not consume extra resource in advance
        // todo: Can't we just invoke createNewWorker here to get the first one up and running?
        for (i in 0 until corePoolSize) {
            workers[i] = PoolWorker(i).apply { start() }
        }

        controlState.value = corePoolSize.toLong()
    }

    /*
     * Closes current scheduler and waits until all threads are stopped.
     * This method uses unsafe API (unconditional unparks, ignoring interruptions etc.)
     * and intended to be used only for testing. Invocation has no additional effect if already closed.
     */
    override fun close() {
        if (!isTerminated.compareAndSet(false, true)) {
            return
        }

        // Race with recently created threads which may park indefinitely
        var finishedThreads = 0
        while (finishedThreads < createdWorkers) {
            var finished = 0
            for (i in 0 until createdWorkers) {
                workers[i]?.also {
                    if (it.isAlive) {
                        // Unparking alive thread is unsafe in general, but acceptable for testing purposes
                        LockSupport.unpark(it)
                        it.join(100)
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
        // TODO at some point make DispatchTask extend TimedTask and make its field settable to save an allocation
        val task = TimedTask(block, schedulerTimeSource.nanoTime(), mode)

        when (submitToLocalQueue(task, mode, fair)) {
            ADDED -> return
            NOT_ADDED -> {
                globalWorkQueue.add(task)
                requestCpuWorker()
            }
            else -> requestCpuWorker()
        }
    }

    /**
     * Unparks or creates a new [PoolWorker] for executing non-blocking tasks if there are idle cores
     */
    private fun requestCpuWorker() {
        // No CPU available -- nothing to request
        if (cpuPermits.availablePermits() == 0) {
            tryUnpark()
            return
        }

        /*
         * Fast path -- we have retired or parked worker, unpark it and we're done.
         * The data race here: when only one permit is available, multiple retired workers
         * can be unparked, but only one will continue execution, so we're overproviding with threads
         * in case of race to avoid spurious starvation
         */
        if (tryUnpark()) return

        /*
         * Create a new thread.
         * It's not preferable to use 'cpuWorkersCounter' here (moreover, it's implicitly here as corePoolSize - cpuPermits.availableTokens),
         * cpuWorkersCounter doesn't take into account threads which are created (and either running or parked), but haven't
         * CPU token: retiring workers, recently unparked workers before `findTask` call, etc.
         * So if we will use cpuWorkersCounter, we start to overprovide with threads too much.
         */
        val state = controlState.value
        val created = createdWorkers(state)
        val blocking = blockingWorkers(state)
        val cpuWorkers = created - blocking
        // If most of created workers are blocking, we should create one more thread to handle non-blocking work
        if (cpuWorkers < corePoolSize && createNewWorker()) {
            return
        }

        // Try unpark again in case there was race between permit release and parking
        tryUnpark()
    }

    private fun tryUnpark(): Boolean {
        while (true) {
            val worker = parkedWorkersStack.pop() ?: return false
            if (!worker.registeredInParkedQueue.value) {
                continue // Someone else succeeded
            } else if (!worker.registeredInParkedQueue.compareAndSet(true, false)) {
                continue // Someone else succeeded
            }

            /*
             * If we successfully took the worker out of the queue, it could be in the following states:
             * 1) Worker is parked, then we'd like to reset its spin and park counters, so after
             *    unpark it will try to steal from every worker at least once
             * 2) Worker is not parked, but it actually idle and
             *    tries to find work. Then idle reset is required as well.
             *    Worker state may be either PARKING or CPU_ACQUIRED (from `findTask`)
             * 3) Worker is active (unparked itself from `idleCpuWorker`), found tasks to do and is currently busy.
             *    Then `idleReset` will do nothing, but we can't distinguish this state from previous
             *    one, so just retry
             */
            worker.idleReset()
            LockSupport.unpark(worker)

            /*
             * Terminating worker could be selected.
             * If it's already TERMINATED we can do nothing, just find another one
             */
            val terminationState = worker.terminationState.value
            if (terminationState == TERMINATED) {
                continue
            }

            /*
             * If not, try to forbid termination and check that new state is not TERMINATED in case of failure.
             * CAS could fail for following reasons:
             * 1) Worker started termination, then bail out
             * 2) Worker just came into blockingWorkerIdle() and set termination state to
             *    'ALLOWED', then proceed, because park will have no effect
             */
            if (!worker.terminationState.compareAndSet(terminationState, FORBIDDEN)
                && worker.terminationState.value == TERMINATED
            ) {
                continue
            }

            if (!worker.isParking) { // Case 2 or 3, just retry
                continue
            }

            return true
        }
    }

    private fun createNewWorker(): Boolean {
        synchronized(workers) {
            val state = controlState.value
            val created = createdWorkers(state)
            val blocking = blockingWorkers(state)
            val cpuWorkers = created - blocking
            // Double check for overprovision
            if (cpuWorkers >= corePoolSize) {
                return false
            }

            if (created >= maxPoolSize || cpuPermits.availablePermits() == 0) {
                return false
            }

            incrementCreatedWorkers()
            require(workers[created] == null)
            val worker = PoolWorker(created).apply { start() }
            workers[created] = worker
            return true
        }
    }

    private fun submitToLocalQueue(task: Task, mode: TaskMode, fair: Boolean): Int {
        val worker = Thread.currentThread() as? PoolWorker ?: return NOT_ADDED
        var result = ADDED

        if (mode == TaskMode.NON_BLOCKING) {
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
                 * to its local queue if it can't acquire CPU
                 */
                val hasPermit = worker.tryAcquireCpu()
                if (!hasPermit) {
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
        var retired = 0
        var finished = 0

        val queueSizes = arrayListOf<String>()
        for (worker in workers) {
            if (worker == null) {
                continue
            }

            val queueSize = worker.localQueue.size()
            when (worker.state) {
                WorkerState.PARKING -> ++parkedWorkers
                WorkerState.BLOCKING -> {
                    ++blockingWorkers
                    queueSizes += queueSize.toString() + "b" // Blocking
                }
                WorkerState.CPU_ACQUIRED -> {
                    ++cpuWorkers
                    queueSizes += queueSize.toString() + "c" // CPU
                }
                WorkerState.RETIRING -> {
                    ++retired
                    if (queueSize > 0) queueSizes += queueSize.toString() + "r" // Retiring
                }
                WorkerState.FINISHED -> ++finished
            }
        }

        return "${super.toString()}[core pool size = $corePoolSize, " +
                "CPU workers = $cpuWorkers, " +
                "blocking workers = $blockingWorkers, " +
                "parked workers = $parkedWorkers, " +
                "retired workers = $retired, " +
                "finished workers = $finished, " +
                "running workers queues = $queueSizes, "+
                "global queue size = ${globalWorkQueue.size()}]"
    }

    // todo: make name of the pool configurable (optional parameter to CoroutineScheduler) and base thread names on it
    internal inner class PoolWorker(sequenceNumber: Int) : Thread("CoroutineScheduler-worker-$sequenceNumber") {
        init {
            isDaemon = true
        }

        // guarded by scheduler lock
        private var indexInArray = sequenceNumber
        val localQueue: WorkQueue = WorkQueue()

        // By default, worker is in RETIRING state in the case when it was created, but all CPU tokens or tasks were taken
        @Volatile
        var state = WorkerState.RETIRING
        val isParking: Boolean get() = state == WorkerState.PARKING
        val isBlocking: Boolean get() = state == WorkerState.BLOCKING
        private val hasCpuPermit: Boolean get() = state == WorkerState.CPU_ACQUIRED

        /**
         * Small state machine for termination.
         * Followed states are allowed:
         * [ALLOWED] -- worker can wake up and terminate itself
         * [FORBIDDEN] -- worker is not allowed to terminate (because it was chosen by another thread to help)
         * [TERMINATED] -- final state, thread is terminating and cannot be resurrected
         *
         * Allowed transitions:
         * [ALLOWED] -> [FORBIDDEN]
         * [ALLOWED] -> [TERMINATED]
         * [FORBIDDEN] -> [ALLOWED]
         */
        val terminationState = atomic(ALLOWED)

        /**
         * Whether worker was added to [parkedWorkersStack].
         * Worker registers itself in this queue once and will stay there until
         * someone will call [Queue.poll] which return it, then this flag is reset.
         */
        val registeredInParkedQueue = atomic(false)
        var nextParkedWorker: PoolWorker? = null

        /**
         * Tries to acquire CPU token if worker doesn't have one
         * @return whether worker has CPU token
         */
        fun tryAcquireCpu(): Boolean {
            return when {
                state == WorkerState.CPU_ACQUIRED -> true
                cpuPermits.tryAcquire() -> {
                    state = WorkerState.CPU_ACQUIRED
                    true
                }
                else -> false
            }
        }

        /**
         * Releases CPU token if worker has any and changes state to [newState]
         * @return whether worker had CPU token
         */
        private fun tryReleaseCpu(newState: WorkerState): Boolean {
            val previousState = state
            val hadCpu = previousState == WorkerState.CPU_ACQUIRED
            if (hadCpu) cpuPermits.release()
            if (previousState != newState) state = newState
            return hadCpu
        }

        /**
         * Time of the last call to [requestCpuWorker] due to missing tasks deadlines.
         * Used as throttling mechanism to avoid unparking multiple threads when it's not necessary
         */
        private var lastExhaustionTime = 0L

        @Volatile // Required for concurrent idleReset
        private var spins = 0L
        private var yields = 0L // TODO replace with IntPair when inline classes arrive

        private var parkTimeNs = MIN_PARK_TIME_NS
        private var rngState = random.nextInt()

        override fun run() {
            while (!isTerminated.value && state != WorkerState.FINISHED) {
                val job = findTask()
                if (job == null) {
                    // Wait for a job with potential park
                    idle()
                } else {
                    idleReset(job.mode)
                    beforeTask(job)
                    runSafely(job.task)
                    afterTask(job)
                }
            }

            tryReleaseCpu(WorkerState.FINISHED)
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
                /*
                 * We should release CPU *before* checking for CPU starvation,
                 * otherwise requestCpuWorker() will not count current thread as blocking
                 */
                incrementBlockingWorkers()
                if (tryReleaseCpu(WorkerState.BLOCKING)) {
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
                decrementBlockingWorkers()
                assert(state == WorkerState.BLOCKING) {"Expected BLOCKING state, but has $state"}
                state = WorkerState.RETIRING
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
                yields <= MAX_YIELDS -> {
                    ++yields
                    yield()
                }
                else -> {
                    if (parkTimeNs < MAX_PARK_TIME_NS) {
                        parkTimeNs = (parkTimeNs * 3 shr 1).coerceAtMost(MAX_PARK_TIME_NS)
                    }

                    if (registeredInParkedQueue.compareAndSet(false, true)) {
                        parkedWorkersStack.push(this)
                    }

                    tryReleaseCpu(WorkerState.PARKING)
                    LockSupport.parkNanos(parkTimeNs)
                }
            }
        }

        private fun blockingWorkerIdle() {
            tryReleaseCpu(WorkerState.PARKING)
            if (registeredInParkedQueue.compareAndSet(false, true)) {
                parkedWorkersStack.push(this)
            }

            terminationState.value = ALLOWED
            val time = System.nanoTime()
            LockSupport.parkNanos(BLOCKING_WORKER_KEEP_ALIVE_NS)
            // Protection against spurious wakeups of parkNanos
            if (System.nanoTime() - time >= BLOCKING_WORKER_KEEP_ALIVE_NS) {
                terminateWorker()
            }
        }

        /**
         * Stops execution of current thread and removes it from [createdWorkers]
         */
        private fun terminateWorker() {
            // Last ditch polling: try to find blocking task before termination
            val task = globalWorkQueue.pollBlockingMode()
            if (task != null) {
                localQueue.add(task, globalWorkQueue)
                return
            }


            synchronized(workers) {
                // Someone else terminated, bail out
                if (createdWorkers <= corePoolSize) {
                    return
                }

                /*
                 * Either thread successfully deregisters itself from queue (and then terminate) or someone else
                 * tried to unpark it. In the latter case we should proceed as unparked worker
                 */
                if (registeredInParkedQueue.value && !registeredInParkedQueue.compareAndSet(true, false)) {
                    return
                }

                /*
                 * See tryUnpark for state reasoning.
                 * If this CAS fails, then we were successfully unparked by other worker and cannot terminate
                 */
                if (!terminationState.compareAndSet(ALLOWED, TERMINATED)) {
                    return
                }

                // At this point this thread is no longer considered as usable for scheduling
                val lastWorkerIndex = decrementCreatedWorkers()
                val worker = workers[lastWorkerIndex]!!
                workers[indexInArray] = worker
                worker.indexInArray = indexInArray
                workers[lastWorkerIndex] = null
            }

            state = WorkerState.FINISHED
        }

        private fun idleReset(mode: TaskMode) {
            if (state == WorkerState.PARKING) {
                assert(mode == TaskMode.PROBABLY_BLOCKING)
                state = WorkerState.BLOCKING
                parkTimeNs = MIN_PARK_TIME_NS
            }

            yields = 0
            spins = 0
        }

        fun idleReset() {
            parkTimeNs = MIN_PARK_TIME_NS
            yields = 0
            spins = 0 // Should be written last
        }


        private fun findTask(): Task? {
            if (tryAcquireCpu()) {
                /*
                 * Anti-starvation mechanism: if pool is overwhelmed by external work
                 * or local work is frequently offloaded, global queue polling will
                 * starve tasks from local queue. But if we never poll global queue,
                 * then local tasks may starve global queue, so poll global queue
                 * once per two core pool size iterations
                 */
                val pollGlobal = nextInt(2 * corePoolSize) == 0
                if (pollGlobal) {
                    globalWorkQueue.poll()?.let { return it }
                }

                localQueue.poll()?.let { return it }
                if (!pollGlobal) {
                    globalWorkQueue.poll()?.let { return it }
                }

                return trySteal()
            }

           /*
            * If the local queue is empty, try to extract blocking task from global queue.
            * It's helpful for two reasons:
            * 1) We won't call excess park/unpark here and someone's else CPU token won't be transferred,
            *    which is a performance win
            * 2) It helps with rare race when external submitter sends depending blocking tasks
            *    one by one and one of the requested workers may miss CPU token
            */
            return localQueue.poll() ?: globalWorkQueue.pollBlockingMode()
        }

        private fun trySteal(): Task? {
            val created = createdWorkers

            // 0 to await an initialization and 1 to avoid excess stealing on single-core machines
            if (created < 2) {
                return null
            }

            val worker = workers[nextInt(created)]
            if (worker !== null && worker !== this) {
                if (localQueue.trySteal(worker.localQueue, globalWorkQueue)) {
                    return localQueue.poll()
                }
            }

            return null
        }
    }

    enum class WorkerState {
        /*
         * Has CPU token and either executes NON_BLOCKING task or
         * tries to steal one (~in busy wait)
         */
        CPU_ACQUIRED,
        // Executing task with Mode.PROBABLY_BLOCKING
        BLOCKING,
        // Currently parked
        PARKING,
        /*
         * Tries to execute its local work
         * and then goes to infinite sleep as no longer needed worker
         */
        RETIRING,
        // Terminal state, will no longer be used
        FINISHED
    }
}
