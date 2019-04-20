/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.io.Closeable
import java.util.*
import java.util.concurrent.*
import java.util.concurrent.locks.*

/**
 * Coroutine scheduler (pool of shared threads) which primary target is to distribute dispatched coroutines over worker threads,
 * including both CPU-intensive and blocking tasks.
 *
 * Current scheduler implementation has two optimization targets:
 * * Efficiency in the face of communication patterns (e.g., actors communicating via channel)
 * * Dynamic resizing to support blocking calls without re-dispatching coroutine to separate "blocking" thread pool
 *
 * ### Structural overview
 *
 * Scheduler consists of [corePoolSize] worker threads to execute CPU-bound tasks and up to [maxPoolSize] (lazily created) threads
 * to execute blocking tasks. Every worker has local queue in addition to global scheduler queue and global queue
 * has priority over local queue to avoid starvation of externally-submitted (e.g., from Android UI thread) tasks and work-stealing is implemented
 * on top of that queues to provide even load distribution and illusion of centralized run queue.
 *
 * ### Scheduling
 *
 * When a coroutine is dispatched from within scheduler worker, it's placed into the head of worker run queue.
 * If the head is not empty, the task from the head is moved to the tail. Though it is unfair scheduling policy,
 * it effectively couples communicating coroutines into one and eliminates scheduling latency that arises from placing task to the end of the queue.
 * Placing former head to the tail is necessary to provide semi-FIFO order, otherwise queue degenerates to stack.
 * When a coroutine is dispatched from an external thread, it's put into the global queue.
 *
 * ### Work stealing and affinity
 *
 * To provide even tasks distribution worker tries to steal tasks from other workers queues before parking when his local queue is empty.
 * A non-standard solution is implemented to provide tasks affinity: task may be stolen only if it's 'stale' enough (based on the value of [WORK_STEALING_TIME_RESOLUTION_NS]).
 * For this purpose monotonic global clock ([System.nanoTime]) is used and every task has associated with it submission time.
 * This approach shows outstanding results when coroutines are cooperative, but as downside scheduler now depends on high-resolution global clock
 * which may limit scalability on NUMA machines.
 *
 * ### Dynamic resizing and support of blocking tasks
 *
 * To support possibly blocking tasks [TaskMode] and CPU quota (via [cpuPermits]) are used.
 * To execute [TaskMode.NON_BLOCKING] tasks from the global queue or to steal tasks from other workers
 * the worker should have CPU permit. When a worker starts executing [TaskMode.PROBABLY_BLOCKING] task,
 * it releases its CPU permit, giving a hint to a scheduler that additional thread should be created (or awaken)
 * if new [TaskMode.NON_BLOCKING] task will arrive. When a worker finishes executing blocking task, it executes
 * all tasks from its local queue (including [TaskMode.NON_BLOCKING]) and then parks as retired without polling
 * global queue or trying to steal new tasks. Such approach may slightly limit scalability (allowing more than [corePoolSize] threads
 * to execute CPU-bound tasks at once), but in practice, it is not, significantly reducing context switches and tasks re-dispatching.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@Suppress("NOTHING_TO_INLINE")
internal class CoroutineScheduler(
    private val corePoolSize: Int,
    private val maxPoolSize: Int,
    private val idleWorkerKeepAliveNs: Long = IDLE_WORKER_KEEP_ALIVE_NS,
    private val schedulerName: String = DEFAULT_SCHEDULER_NAME
) : Executor, Closeable {
    init {
        require(corePoolSize >= MIN_SUPPORTED_POOL_SIZE) {
            "Core pool size $corePoolSize should be at least $MIN_SUPPORTED_POOL_SIZE"
        }
        require(maxPoolSize >= corePoolSize) {
            "Max pool size $maxPoolSize should be greater than or equals to core pool size $corePoolSize"
        }
        require(maxPoolSize <= MAX_SUPPORTED_POOL_SIZE) {
            "Max pool size $maxPoolSize should not exceed maximal supported number of threads $MAX_SUPPORTED_POOL_SIZE"
        }
        require(idleWorkerKeepAliveNs > 0) {
            "Idle worker keep alive time $idleWorkerKeepAliveNs must be positive"
        }
    }

    private val globalQueue: GlobalQueue = GlobalQueue()

    /**
     * Permits to execute non-blocking (~CPU-intensive) tasks.
     * If worker owns a permit, it can schedule non-blocking tasks to its queue and steal work from other workers.
     * If worker doesn't, it can execute only blocking tasks (and non-blocking leftovers from its local queue)
     * and will try to park as soon as its queue is empty.
     */
    private val cpuPermits = Semaphore(corePoolSize, false)

    /**
     * The stack of parker workers.
     * Every worker registers itself in a stack before parking (if it was not previously registered)
     * and callers of [requestCpuWorker] will try to unpark a thread from the top of a stack.
     * This is a form of intrusive garbage-free Treiber stack where Worker also is a stack node.
     *
     * The stack is better than a queue (even with contention on top) because it unparks threads
     * in most-recently used order, improving both performance and locality.
     * Moreover, it decreases threads thrashing, if the pool has n threads when only n / 2 is required,
     * the latter half will never be unparked and will terminate itself after [IDLE_WORKER_KEEP_ALIVE_NS].
     *
     * This long version consist of version bits with [PARKED_VERSION_MASK]
     * and top worker thread index bits with [PARKED_INDEX_MASK].
     */
    private val parkedWorkersStack = atomic(0L)

    /**
     * Updates index of the worker at the top of [parkedWorkersStack].
     * It always updates version to ensure interference with [parkedWorkersStackPop] operation
     * that might have already decided to put this index to the top.
     *
     * Note, [newIndex] can be zero for the worker that is being terminated (removed from [workers]).
     */
    private fun parkedWorkersStackTopUpdate(worker: Worker, oldIndex: Int, newIndex: Int) {
        parkedWorkersStack.loop { top ->
            val index = (top and PARKED_INDEX_MASK).toInt()
            val updVersion = (top + PARKED_VERSION_INC) and PARKED_VERSION_MASK
            val updIndex = if (index == oldIndex) {
                if (newIndex == 0) {
                    parkedWorkersStackNextIndex(worker)
                } else {
                    newIndex
                }
            } else {
                index // no change to index, but update version
            }
            if (updIndex < 0) return@loop // retry
            if (parkedWorkersStack.compareAndSet(top, updVersion or updIndex.toLong())) return
        }
    }

    /**
     * Pushes worker into [parkedWorkersStack].
     * It does nothing is this worker is already physically linked to the stack.
     * This method is invoked only from the worker thread itself.
     * This invocation always precedes [LockSupport.parkNanos].
     * See [Worker.doPark].
     */
    private fun parkedWorkersStackPush(worker: Worker) {
        if (worker.nextParkedWorker !== NOT_IN_STACK) return // already in stack, bail out
        /*
         * The below loop can be entered only if this worker was not in the stack and, since no other thread
         * can add it to the stack (only the worker itself), this invariant holds while this loop executes.
         */
        parkedWorkersStack.loop { top ->
            val index = (top and PARKED_INDEX_MASK).toInt()
            val updVersion = (top + PARKED_VERSION_INC) and PARKED_VERSION_MASK
            val updIndex = worker.indexInArray
            assert(updIndex != 0) // only this worker can push itself, cannot be terminated
            worker.nextParkedWorker = workers[index]
            /*
             * Other thread can be changing this worker's index at this point, but it
             * also invokes parkedWorkersStackTopUpdate which updates version to make next CAS fail.
             * Successful CAS of the stack top completes successful push.
             */
            if (parkedWorkersStack.compareAndSet(top, updVersion or updIndex.toLong())) return
        }
    }

    /**
     * Pops worker from [parkedWorkersStack].
     * It can be invoked concurrently from any thread that is looking for help and needs to unpark some worker.
     * This invocation is always followed by an attempt to [LockSupport.unpark] resulting worker.
     * See [tryUnpark].
     */
    private fun parkedWorkersStackPop(): Worker? {
        parkedWorkersStack.loop { top ->
            val index = (top and PARKED_INDEX_MASK).toInt()
            val worker = workers[index] ?: return null // stack is empty
            val updVersion = (top + PARKED_VERSION_INC) and PARKED_VERSION_MASK
            val updIndex = parkedWorkersStackNextIndex(worker)
            if (updIndex < 0) return@loop // retry
            /*
             * Other thread can be changing this worker's index at this point, but it
             * also invokes parkedWorkersStackTopUpdate which updates version to make next CAS fail.
             * Successful CAS of the stack top completes successful pop.
             */
            if (parkedWorkersStack.compareAndSet(top, updVersion or updIndex.toLong())) {
                /*
                 * We've just took worker out of the stack, but nextParkerWorker is not reset yet, so if a worker is
                 * currently invoking parkedWorkersStackPush it would think it is in the stack and bail out without
                 * adding itself again. It does not matter, since we are going it invoke unpark on the thread
                 * that was popped out of parkedWorkersStack anyway.
                 */
                worker.nextParkedWorker = NOT_IN_STACK
                return worker
            }
        }
    }

    /**
     * Finds next usable index for [parkedWorkersStack]. The problem is that workers can
     * be terminated at their [Worker.indexInArray] becomes zero, so they cannot be
     * put at the top of the stack. In which case we are looking for next.
     *
     * Returns `index >= 0` or `-1` for retry.
     */
    private fun parkedWorkersStackNextIndex(worker: Worker): Int {
        var next = worker.nextParkedWorker
        findNext@ while (true) {
            when {
                next === NOT_IN_STACK -> return -1 // we are too late -- other thread popped this element, retry
                next === null -> return 0 // stack becomes empty
                else -> {
                    val nextWorker = next as Worker
                    val updIndex = nextWorker.indexInArray
                    if (updIndex != 0) return updIndex // found good index for next worker
                    // Otherwise, this worker was terminated and we cannot put it to top anymore, check next
                    next = nextWorker.nextParkedWorker
                }
            }
        }
    }

    /**
     * State of worker threads.
     * [workers] is array of lazily created workers up to [maxPoolSize] workers.
     * [createdWorkers] is count of already created workers (worker with index lesser than [createdWorkers] exists).
     * [blockingWorkers] is count of running workers which are executing [TaskMode.PROBABLY_BLOCKING] task.
     * All mutations of array's content are guarded by lock.
     *
     * **NOTE**: `workers[0]` is always `null` (never used, works as sentinel value), so
     * workers are 1-indexed, code path in [Worker.trySteal] is a bit faster and index swap during termination
     * works properly
     */
    private val workers: Array<Worker?> = arrayOfNulls(maxPoolSize + 1)

    /**
     * Long describing state of workers in this pool.
     * Currently includes created and blocking workers each occupying [BLOCKING_SHIFT] bits.
     */
    private val controlState = atomic(0L)

    private val createdWorkers: Int inline get() = (controlState.value and CREATED_MASK).toInt()
    private val blockingWorkers: Int inline get() = (controlState.value and BLOCKING_MASK shr BLOCKING_SHIFT).toInt()

    private inline fun createdWorkers(state: Long): Int = (state and CREATED_MASK).toInt()
    private inline fun blockingWorkers(state: Long): Int = (state and BLOCKING_MASK shr BLOCKING_SHIFT).toInt()

    // Guarded by synchronization
    private inline fun incrementCreatedWorkers(): Int = createdWorkers(controlState.incrementAndGet())
    private inline fun decrementCreatedWorkers(): Int = createdWorkers(controlState.getAndDecrement())

    private inline fun incrementBlockingWorkers() { controlState.addAndGet(1L shl BLOCKING_SHIFT) }
    private inline fun decrementBlockingWorkers() { controlState.addAndGet(-(1L shl BLOCKING_SHIFT)) }

    private val random = Random()

    // This is used a "stop signal" for close and shutdown functions
    private val _isTerminated = atomic(0) // todo: replace with atomic boolean on new versions of atomicFu
    private val isTerminated: Boolean get() = _isTerminated.value != 0

    companion object {
        private val MAX_SPINS = systemProp("kotlinx.coroutines.scheduler.spins", 1000, minValue = 1)
        private val MAX_YIELDS = MAX_SPINS + systemProp("kotlinx.coroutines.scheduler.yields", 0, minValue = 0)

        @JvmStatic // Note, that is fits into Int (it is equal to 10^9)
        private val MAX_PARK_TIME_NS = TimeUnit.SECONDS.toNanos(1).toInt()

        @JvmStatic
        private val MIN_PARK_TIME_NS = (WORK_STEALING_TIME_RESOLUTION_NS / 4)
            .coerceAtLeast(10)
            .coerceAtMost(MAX_PARK_TIME_NS.toLong()).toInt()

        // A symbol to mark workers that are not in parkedWorkersStack
        private val NOT_IN_STACK = Symbol("NOT_IN_STACK")

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
        private const val BLOCKING_SHIFT = 21 // 2M threads max
        private const val CREATED_MASK: Long = (1L shl BLOCKING_SHIFT) - 1
        private const val BLOCKING_MASK: Long = CREATED_MASK shl BLOCKING_SHIFT

        internal const val MIN_SUPPORTED_POOL_SIZE = 1 // we support 1 for test purposes, but it is not usually used
        internal const val MAX_SUPPORTED_POOL_SIZE = (1 shl BLOCKING_SHIFT) - 2

        // Masks of parkedWorkersStack
        private const val PARKED_INDEX_MASK = CREATED_MASK
        private const val PARKED_VERSION_MASK = CREATED_MASK.inv()
        private const val PARKED_VERSION_INC = 1L shl BLOCKING_SHIFT
    }

    override fun execute(command: Runnable) = dispatch(command)

    override fun close() = shutdown(10_000L)

    // Shuts down current scheduler and waits until all work is done and all threads are stopped.
    fun shutdown(timeout: Long) {
        // atomically set termination flag which is checked when workers are added or removed
        if (!_isTerminated.compareAndSet(0, 1)) return
        // make sure we are not waiting for the current thread
        val currentWorker = currentWorker()
        // Capture # of created workers that cannot change anymore (mind the synchronized block!)
        val created = synchronized(workers) { createdWorkers }
        // Shutdown all workers with the only exception of the current thread
        for (i in 1..created) {
            val worker = workers[i]!!
            if (worker !== currentWorker) {
                while (worker.isAlive) {
                    LockSupport.unpark(worker)
                    worker.join(timeout)
                }
                val state = worker.state
                check(state === WorkerState.TERMINATED) { "Expected TERMINATED state, but found $state"}
                worker.localQueue.offloadAllWork(globalQueue)
            }
        }
        // Make sure no more work is added to GlobalQueue from anywhere
        globalQueue.close()
        // Finish processing tasks from globalQueue and/or from this worker's local queue
        while (true) {
            val task = currentWorker?.findTask() ?: globalQueue.removeFirstOrNull() ?: break
            runSafely(task)
        }
        // Shutdown current thread
        currentWorker?.tryReleaseCpu(WorkerState.TERMINATED)
        // check & cleanup state
        assert(cpuPermits.availablePermits() == corePoolSize)
        parkedWorkersStack.value = 0L
        controlState.value = 0L
    }

    /**
     * Dispatches execution of a runnable [block] with a hint to a scheduler whether
     * this [block] may execute blocking operations (IO, system calls, locking primitives etc.)
     *
     * @param block runnable to be dispatched
     * @param taskContext concurrency context of given [block]
     * @param fair whether the task should be dispatched fairly (strict FIFO) or not (semi-FIFO)
     */
    fun dispatch(block: Runnable, taskContext: TaskContext = NonBlockingContext, fair: Boolean = false) {
        timeSource.trackTask() // this is needed for virtual time support
        val task = createTask(block, taskContext)
        // try to submit the task to the local queue and act depending on the result
        when (submitToLocalQueue(task, fair)) {
            ADDED -> return
            NOT_ADDED -> {
                // try to offload task to global queue
                if (!globalQueue.addLast(task)) {
                    // Global queue is closed in the last step of close/shutdown -- no more tasks should be accepted
                    throw RejectedExecutionException("$schedulerName was terminated")
                }
                requestCpuWorker()
            }
            else -> requestCpuWorker() // ask for help
        }
    }

    internal fun createTask(block: Runnable, taskContext: TaskContext): Task {
        val nanoTime = schedulerTimeSource.nanoTime()
        if (block is Task) {
            block.submissionTime = nanoTime
            block.taskContext = taskContext
            return block
        }
        return TaskImpl(block, nanoTime, taskContext)
    }

    /**
     * Unparks or creates a new [Worker] for executing non-blocking tasks if there are idle cores
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
        /*
         * We check how many threads are there to handle non-blocking work,
         * and create one more if we have not enough of them.
         */
        if (cpuWorkers < corePoolSize) {
            val newCpuWorkers = createNewWorker()
            // If we've created the first cpu worker and corePoolSize > 1 then create
            // one more (second) cpu worker, so that stealing between them is operational
            if (newCpuWorkers == 1 && corePoolSize > 1) createNewWorker()
            if (newCpuWorkers > 0) return
        }
        // Try unpark again in case there was race between permit release and parking
        tryUnpark()
    }

    private fun tryUnpark(): Boolean {
        while (true) {
            val worker = parkedWorkersStackPop() ?: return false
            /*
             * If we successfully took the worker out of the queue, it could be in the following states:
             * 1) Worker is parked, then we'd like to reset its spin and park counters, so after
             *    unpark it will try to steal from every worker at least once
             * 2) Worker is not parked, but it actually idle and
             *    tries to find work. Then idle reset is required as well.
             *    Worker state may be either PARKING or CPU_ACQUIRED (from `findTask`)
             * 3) Worker is active (unparked itself from `idleCpuWorker`), found tasks to do and is currently busy.
             *    Then `idleResetBeforeUnpark` will do nothing, but we can't distinguish this state from previous
             *    one, so just retry.
             * 4) Worker is terminated. No harm in resetting its counters either.
             */
            worker.idleResetBeforeUnpark()
            /*
             * Check that the thread we've found in the queue was indeed in parking state, before we
             * actually try to unpark it. 
             */
            val wasParking = worker.isParking
            /*
             * Send unpark signal anyway, because the thread may have made decision to park but have not yet set its
             * state to parking and this could be the last thread we have (unparking random thread would not harm).
             */
            LockSupport.unpark(worker)
            /*
             * If this thread was not in parking state then we definitely need to find another thread.
             * We err on the side of unparking more threads than needed here.
             */
            if (!wasParking) continue
            /*
             * Terminating worker could be selected.
             * If it's already TERMINATED or we cannot forbid it from terminating, then try find another worker.
             */
            if (!worker.tryForbidTermination()) continue
            /*
             * Here we've successfully unparked a thread that was parked and had forbidden it from making
             * decision to terminate, so we are now sure we've got some help.
             */
            return true
        }
    }

    /*
     * Returns the number of CPU workers after this function (including new worker) or
     * 0 if no worker was created.
     */
    private fun createNewWorker(): Int {
        synchronized(workers) {
            // Make sure we're not trying to resurrect terminated scheduler
            if (isTerminated) return -1
            val state = controlState.value
            val created = createdWorkers(state)
            val blocking = blockingWorkers(state)
            val cpuWorkers = created - blocking
            // Double check for overprovision
            if (cpuWorkers >= corePoolSize) return 0
            if (created >= maxPoolSize || cpuPermits.availablePermits() == 0) return 0
            // start & register new worker, commit index only after successful creation
            val newIndex = createdWorkers + 1
            require(newIndex > 0 && workers[newIndex] == null)
            val worker = Worker(newIndex).apply { start() }
            require(newIndex == incrementCreatedWorkers())
            workers[newIndex] = worker
            return cpuWorkers + 1
        }
    }

    /**
     * Returns [ADDED], or [NOT_ADDED], or [ADDED_REQUIRES_HELP].
     */
    private fun submitToLocalQueue(task: Task, fair: Boolean): Int {
        val worker = currentWorker() ?: return NOT_ADDED

        /*
         * This worker could have been already terminated from this thread by close/shutdown and it should not
         * accept any more tasks into its local queue.
         */
        if (worker.state === WorkerState.TERMINATED) return NOT_ADDED

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
                 * to its local queue if it can't acquire CPU
                 */
                val hasPermit = worker.tryAcquireCpuPermit()
                if (!hasPermit) {
                    return NOT_ADDED
                }
            }
        }

        val noOffloadingHappened = if (fair) {
            worker.localQueue.addLast(task, globalQueue)
        } else {
            worker.localQueue.add(task, globalQueue)
        }

        if (noOffloadingHappened) {
            // When we're close to queue capacity, wake up anyone to steal work
            // Note: non-atomic bufferSize here is Ok (it is just a performance optimization)
            if (worker.localQueue.bufferSize > QUEUE_SIZE_OFFLOAD_THRESHOLD) {
                return ADDED_REQUIRES_HELP
            }
            return result
        }
        return ADDED_REQUIRES_HELP
    }

    private fun currentWorker(): Worker? = (Thread.currentThread() as? Worker)?.takeIf { it.scheduler == this }

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
        var terminated = 0
        val queueSizes = arrayListOf<String>()
        for (worker in workers) {
            if (worker == null) continue
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
                WorkerState.TERMINATED -> ++terminated
            }
        }
        val state = controlState.value
        return "$schedulerName@$hexAddress[" +
                "Pool Size {" +
                    "core = $corePoolSize, " +
                    "max = $maxPoolSize}, " +
                "Worker States {" +
                    "CPU = $cpuWorkers, " +
                    "blocking = $blockingWorkers, " +
                    "parked = $parkedWorkers, " +
                    "retired = $retired, " +
                    "terminated = $terminated}, " +
                "running workers queues = $queueSizes, "+
                "global queue size = ${globalQueue.size}, " +
                "Control State Workers {" +
                    "created = ${createdWorkers(state)}, " +
                    "blocking = ${blockingWorkers(state)}}" +
                "]"
    }

    private fun runSafely(task: Task) {
        try {
            task.run()
        } catch (e: Throwable) {
            val thread = Thread.currentThread()
            thread.uncaughtExceptionHandler.uncaughtException(thread, e)
        } finally {
            timeSource.unTrackTask()
        }
    }

    internal inner class Worker private constructor() : Thread() {
        init {
            isDaemon = true
        }

        // guarded by scheduler lock, index in workers array, 0 when not in array (terminated)
        @Volatile // volatile for push/pop operation into parkedWorkersStack
        var indexInArray = 0
            set(index) {
                name = "$schedulerName-worker-${if (index == 0) "TERMINATED" else index.toString()}"
                field = index
            }

        constructor(index: Int) : this() {
            indexInArray = index
        }

        val scheduler get() = this@CoroutineScheduler

        val localQueue: WorkQueue = WorkQueue()

        /**
         * Worker state. **Updated only by this worker thread**.
         * By default, worker is in RETIRING state in the case when it was created, but all CPU tokens or tasks were taken.
         */
        @Volatile
        var state = WorkerState.RETIRING

        val isParking: Boolean get() = state == WorkerState.PARKING
        val isBlocking: Boolean get() = state == WorkerState.BLOCKING

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
        private val terminationState = atomic(ALLOWED)

        /**
         * It is set to the termination deadline when started doing [blockingWorkerIdle] and it reset
         * when there is a task. It servers as protection against spurious wakeups of parkNanos.
         */
        private var terminationDeadline = 0L

        /**
         * Reference to the next worker in the [parkedWorkersStack].
         * It may be `null` if there is no next parked worker.
         * This reference is set to [NOT_IN_STACK] when worker is physically not in stack.
         */
        @Volatile
        var nextParkedWorker: Any? = NOT_IN_STACK

        /**
         * Tries to set [terminationState] to [FORBIDDEN], returns `false` if this attempt fails.
         * This attempt may fail either because worker terminated itself or because someone else
         * claimed this worker (though this case is rare, because require very bad timings)
         */
        fun tryForbidTermination(): Boolean {
            val state = terminationState.value
            return when (state) {
                TERMINATED -> false // already terminated
                FORBIDDEN -> false // already forbidden, someone else claimed this worker
                ALLOWED -> terminationState.compareAndSet(
                    ALLOWED,
                    FORBIDDEN
                )
                else -> error("Invalid terminationState = $state")
            }
        }

        /**
         * Tries to acquire CPU token if worker doesn't have one
         * @return whether worker has CPU token
         */
        fun tryAcquireCpuPermit(): Boolean {
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
        internal fun tryReleaseCpu(newState: WorkerState): Boolean {
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

        @Volatile // Required for concurrent idleResetBeforeUnpark
        private var spins = 0 // spins until MAX_SPINS, then yields until MAX_YIELDS

        // Note: it is concurrently reset by idleResetBeforeUnpark
        private var parkTimeNs = MIN_PARK_TIME_NS

        private var rngState = random.nextInt()
        private var lastStealIndex = 0 // try in order repeated, reset when unparked

        override fun run() {
            var wasIdle = false // local variable to avoid extra idleReset invocations when tasks repeatedly arrive
            while (!isTerminated && state != WorkerState.TERMINATED) {
                val task = findTask()
                if (task == null) {
                    // Wait for a job with potential park
                    if (state == WorkerState.CPU_ACQUIRED) {
                        cpuWorkerIdle()
                    } else {
                        blockingWorkerIdle()
                    }
                    wasIdle = true
                } else {
                    // Note: read task.mode before running the task, because Task object will be reused after run
                    val taskMode = task.mode
                    if (wasIdle) {
                        idleReset(taskMode)
                        wasIdle = false
                    }
                    beforeTask(taskMode, task.submissionTime)
                    runSafely(task)
                    afterTask(taskMode)
                }
            }
            tryReleaseCpu(WorkerState.TERMINATED)
        }

        private fun beforeTask(taskMode: TaskMode, taskSubmissionTime: Long) {
            if (taskMode != TaskMode.NON_BLOCKING) {
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
            if (now - taskSubmissionTime >= WORK_STEALING_TIME_RESOLUTION_NS &&
                now - lastExhaustionTime >= WORK_STEALING_TIME_RESOLUTION_NS * 5
            ) {
                lastExhaustionTime = now
                requestCpuWorker()
            }
        }

        private fun afterTask(taskMode: TaskMode) {
            if (taskMode != TaskMode.NON_BLOCKING) {
                decrementBlockingWorkers()
                val currentState = state
                // Shutdown sequence of blocking dispatcher
                if (currentState !== WorkerState.TERMINATED) {
                    assert(currentState == WorkerState.BLOCKING) { "Expected BLOCKING state, but has $currentState" }
                    state = WorkerState.RETIRING
                }
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

        private fun cpuWorkerIdle() {
            /*
             * Simple adaptive await of work:
             * Spin on the volatile field with an empty loop in hope that new work will arrive,
             * then start yielding to reduce CPU pressure, and finally start adaptive parking.
             *
             * The main idea is not to park while it's possible (otherwise throughput on asymmetric workloads suffers due to too frequent
             * park/unpark calls and delays between job submission and thread queue checking)
             */
            val spins = this.spins // volatile read
            if (spins <= MAX_YIELDS) {
                this.spins = spins + 1 // volatile write
                if (spins >= MAX_SPINS) yield()
            } else {
                if (parkTimeNs < MAX_PARK_TIME_NS) {
                    parkTimeNs = (parkTimeNs * 3 ushr 1).coerceAtMost(MAX_PARK_TIME_NS)
                }
                tryReleaseCpu(WorkerState.PARKING)
                doPark(parkTimeNs.toLong())
            }
        }

        private fun blockingWorkerIdle() {
            tryReleaseCpu(WorkerState.PARKING)
            if (!blockingQuiescence()) return
            terminationState.value = ALLOWED
            // set termination deadline the first time we are here (it is reset in idleReset)
            if (terminationDeadline == 0L) terminationDeadline = System.nanoTime() + idleWorkerKeepAliveNs
            // actually park
            if (!doPark(idleWorkerKeepAliveNs)) return
            // try terminate when we are idle past termination deadline
            // note, that comparison is written like this to protect against potential nanoTime wraparound
            if (System.nanoTime() - terminationDeadline >= 0) {
                terminationDeadline = 0L // if attempt to terminate worker fails we'd extend deadline again
                tryTerminateWorker()
            }
        }

        private fun doPark(nanos: Long): Boolean {
            /*
             * Here we are trying to park, then check whether there are new blocking tasks
             * (because submitting thread could have missed this thread in tryUnpark)
             */
            parkedWorkersStackPush(this)
            if (!blockingQuiescence()) return false
            LockSupport.parkNanos(nanos)
            return true
        }

        /**
         * Stops execution of current thread and removes it from [createdWorkers].
         */
        private fun tryTerminateWorker() {
            synchronized(workers) {
                // Make sure we're not trying race with termination of scheduler
                if (isTerminated) return
                // Someone else terminated, bail out
                if (createdWorkers <= corePoolSize) return
                // Try to find blocking task before termination
                if (!blockingQuiescence()) return
                /*
                 * See tryUnpark for state reasoning.
                 * If this CAS fails, then we were successfully unparked by other worker and cannot terminate.
                 */
                if (!terminationState.compareAndSet(ALLOWED, TERMINATED)) return
                /*
                 * At this point this thread is no longer considered as usable for scheduling.
                 * We need multi-step choreography to reindex workers.
                 *
                 * 1) Read current worker's index and reset it to zero.
                 */
                val oldIndex = indexInArray
                indexInArray = 0
                /*
                 * Now this worker cannot become the top of parkedWorkersStack, but it can
                 * still be at the stack top via oldIndex.
                 *
                 * 2) Update top of stack if it was pointing to oldIndex and make sure no
                 *    pending push/pop operation that might have already retrieved oldIndex could complete.
                 */
                parkedWorkersStackTopUpdate(this, oldIndex, 0)
                /*
                 * 3) Move last worker into an index in array that was previously occupied by this worker,
                 *    if last worker was a different one (sic!).
                 */
                val lastIndex = decrementCreatedWorkers()
                if (lastIndex != oldIndex) {
                    val lastWorker = workers[lastIndex]!!
                    workers[oldIndex] = lastWorker
                    lastWorker.indexInArray = oldIndex
                    /*
                     * Now lastWorker is available at both indices in the array, but it can
                     * still be at the stack top on via its lastIndex
                     *
                     * 4) Update top of stack lastIndex -> oldIndex and make sure no
                     *    pending push/pop operation that might have already retrieved lastIndex could complete.
                     */
                    parkedWorkersStackTopUpdate(lastWorker, lastIndex, oldIndex)
                }
                /*
                 * 5) It is safe to clear reference from workers array now.
                 */
                workers[lastIndex] = null
            }
            state = WorkerState.TERMINATED
        }

        /**
         * Checks whether new blocking tasks arrived to the pool when worker decided
         * it can go to deep park/termination and puts recently arrived task to its local queue.
         * Returns `true` if there is no blocking tasks in the queue.
         */
        private fun blockingQuiescence(): Boolean {
            globalQueue.removeFirstWithModeOrNull(TaskMode.PROBABLY_BLOCKING)?.let {
                localQueue.add(it, globalQueue)
                return false
            }
            return true
        }

        // It is invoked by this worker when it finds a task
        private fun idleReset(mode: TaskMode) {
            terminationDeadline = 0L // reset deadline for termination
            lastStealIndex = 0 // reset steal index (next time try random)
            if (state == WorkerState.PARKING) {
                assert(mode == TaskMode.PROBABLY_BLOCKING)
                state = WorkerState.BLOCKING
                parkTimeNs = MIN_PARK_TIME_NS
            }
            spins = 0
        }

        // It is invoked by other thread before this worker is unparked
        fun idleResetBeforeUnpark() {
            parkTimeNs = MIN_PARK_TIME_NS
            spins = 0 // Volatile write, should be written last
        }

        internal fun findTask(): Task? {
            if (tryAcquireCpuPermit()) return findTaskWithCpuPermit()
            /*
             * If the local queue is empty, try to extract blocking task from global queue.
             * It's helpful for two reasons:
             * 1) We won't call excess park/unpark here and someone's else CPU token won't be transferred,
             *    which is a performance win
             * 2) It helps with rare race when external submitter sends depending blocking tasks
             *    one by one and one of the requested workers may miss CPU token
             */
            return localQueue.poll() ?: globalQueue.removeFirstWithModeOrNull(TaskMode.PROBABLY_BLOCKING)
        }

        private fun findTaskWithCpuPermit(): Task? {
            /*
             * Anti-starvation mechanism: if pool is overwhelmed by external work
             * or local work is frequently offloaded, global queue polling will
             * starve tasks from local queue. But if we never poll global queue,
             * then local tasks may starve global queue, so poll global queue
             * once per two core pool size iterations.
             * Poll global queue only for non-blocking tasks as for blocking task a separate thread was woken up.
             * If current thread is woken up, then its local queue is empty and it will poll global queue anyway,
             * otherwise current thread may already have blocking task in its local queue.
             */
            val globalFirst = nextInt(2 * corePoolSize) == 0
            if (globalFirst) globalQueue.removeFirstWithModeOrNull(TaskMode.NON_BLOCKING)?.let { return it }
            localQueue.poll()?.let { return it }
            if (!globalFirst) globalQueue.removeFirstOrNull()?.let { return it }
            return trySteal()
        }

        private fun trySteal(): Task? {
            val created = createdWorkers
            // 0 to await an initialization and 1 to avoid excess stealing on single-core machines
            if (created < 2) return null

            // TODO to guarantee quiescence it's probably worth to do a full scan
            var stealIndex = lastStealIndex
            if (stealIndex == 0) stealIndex = nextInt(created) // start with random steal index
            stealIndex++ // then go sequentially
            if (stealIndex > created) stealIndex = 1
            lastStealIndex = stealIndex
            val worker = workers[stealIndex]
            if (worker !== null && worker !== this) {
                if (localQueue.trySteal(worker.localQueue, globalQueue)) {
                    return localQueue.poll()
                }
            }
            return null
        }
    }

    enum class WorkerState {
        /**
         * Has CPU token and either executes [TaskMode.NON_BLOCKING] task or tries to steal one
         */
        CPU_ACQUIRED,

        /**
         * Executing task with [TaskMode.PROBABLY_BLOCKING].
         */
        BLOCKING,

        /**
         * Currently parked.
         */
        PARKING,

        /**
         * Tries to execute its local work and then goes to infinite sleep as no longer needed worker.
         */
        RETIRING,

        /**
         * Terminal state, will no longer be used
         */
        TERMINATED
    }
}
