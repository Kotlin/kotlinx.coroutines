/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.io.*
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import java.util.concurrent.locks.*
import kotlin.math.*
import kotlin.random.*

/**
 * Coroutine scheduler (pool of shared threads) which primary target is to distribute dispatched coroutines
 * over worker threads, including both CPU-intensive and blocking tasks, is the most efficient manner.
 *
 * Current scheduler implementation has two optimization targets:
 * * Efficiency in the face of communication patterns (e.g., actors communicating via channel)
 * * Dynamic resizing to support blocking calls without re-dispatching coroutine to separate "blocking" thread pool.
 *
 * ### Structural overview
 *
 * Scheduler consists of [corePoolSize] worker threads to execute CPU-bound tasks and up to
 * [maxPoolSize] lazily created  threads to execute blocking tasks.
 * Every worker has a local queue in addition to a global scheduler queue
 * and the global queue has priority over local queue to avoid starvation of externally-submitted
 * (e.g. from Android UI thread) tasks.
 * Work-stealing is implemented on top of that queues to provide
 * even load distribution and illusion of centralized run queue.
 *
 * ### Scheduling policy
 *
 * When a coroutine is dispatched from within a scheduler worker, it's placed into the head of worker run queue.
 * If the head is not empty, the task from the head is moved to the tail. Though it is an unfair scheduling policy,
 * it effectively couples communicating coroutines into one and eliminates scheduling latency
 * that arises from placing tasks to the end of the queue.
 * Placing former head to the tail is necessary to provide semi-FIFO order, otherwise, queue degenerates to stack.
 * When a coroutine is dispatched from an external thread, it's put into the global queue.
 * The original idea with a single-slot LIFO buffer comes from Golang runtime scheduler by D. Vyukov.
 * It was proven to be "fair enough", performant and generally well accepted and initially was a significant inspiration
 * source for the coroutine scheduler.
 *
 * ### Work stealing and affinity
 *
 * To provide even tasks distribution worker tries to steal tasks from other workers queues
 * before parking when his local queue is empty.
 * A non-standard solution is implemented to provide tasks affinity: a task from FIFO buffer may be stolen
 * only if it is stale enough based on the value of [WORK_STEALING_TIME_RESOLUTION_NS].
 * For this purpose, monotonic global clock is used, and every task has associated with its submission time.
 * This approach shows outstanding results when coroutines are cooperative,
 * but as downside scheduler now depends on a high-resolution global clock,
 * which may limit scalability on NUMA machines. Tasks from LIFO buffer can be stolen on a regular basis.
 *
 * ### Thread management
 * One of the hardest parts of the scheduler is decentralized management of the threads with the progress guarantees
 * similar to the regular centralized executors.
 * The state of the threads consists of [controlState] and [parkedWorkersStack] fields.
 * The former field incorporates the amount of created threads, CPU-tokens and blocking tasks
 * that require a thread compensation,
 * while the latter represents intrusive versioned Treiber stack of idle workers.
 * When a worker cannot find any work, they first add themselves to the stack,
 * then re-scans the queue to avoid missing signals and then attempts to park
 * with additional rendezvous against unnecessary parking.
 * If a worker finds a task that it cannot yet steal due to time constraints, it stores this fact in its state
 * (to be uncounted when additional work is signalled) and parks for such duration.
 *
 * When a new task arrives in the scheduler (whether it is local or global queue),
 * either an idle worker is being signalled, or a new worker is attempted to be created.
 * Only [corePoolSize] workers can be created for regular CPU tasks)
 *
 * ### Support for blocking tasks
 * The scheduler also supports the notion of [blocking][TASK_PROBABLY_BLOCKING] tasks.
 * When executing or enqueuing blocking tasks, the scheduler notifies or creates one more worker in
 * addition to core pool size, so at any given moment, it has [corePoolSize] threads (potentially not yet created)
 * to serve CPU-bound tasks. To properly guarantee liveness, the scheduler maintains
 * "CPU permits" -- [corePoolSize] special tokens that permit an arbitrary worker to execute and steal CPU-bound tasks.
 * When worker encounters blocking tasks, it basically hands off its permit to another thread (not directly though) to
 * keep invariant "scheduler always has at least min(pending CPU tasks, core pool size)
 * and at most core pool size threads to execute CPU tasks".
 * To avoid overprovision, workers without CPU permit are allowed to scan [globalBlockingQueue]
 * and steal **only** blocking tasks from other workers.
 *
 * The scheduler does not limit the count of pending blocking tasks, potentially creating up to [maxPoolSize] threads.
 * End users do not have access to the scheduler directly and can dispatch blocking tasks only with
 * [LimitingDispatcher] that does control concurrency level by its own mechanism.
 */
@Suppress("NOTHING_TO_INLINE")
internal class CoroutineScheduler(
    @JvmField val corePoolSize: Int,
    @JvmField val maxPoolSize: Int,
    @JvmField val idleWorkerKeepAliveNs: Long = IDLE_WORKER_KEEP_ALIVE_NS,
    @JvmField val schedulerName: String = DEFAULT_SCHEDULER_NAME
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

    @JvmField
    val globalCpuQueue = GlobalQueue()
    @JvmField
    val globalBlockingQueue = GlobalQueue()

    private fun addToGlobalQueue(task: Task): Boolean {
        return if (task.isBlocking) {
            globalBlockingQueue.addLast(task)
        } else {
            globalCpuQueue.addLast(task)
        }
    }

    /**
     * The stack of parker workers.
     * Every worker registers itself in a stack before parking (if it was not previously registered),
     * so it can be signalled when new tasks arrive.
     * This is a form of intrusive garbage-free Treiber stack where [Worker] also is a stack node.
     *
     * The stack is better than a queue (even with the contention on top) because it unparks threads
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
    internal fun parkedWorkersStackTopUpdate(worker: Worker, oldIndex: Int, newIndex: Int) {
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
     *
     * Returns `true` if worker was added to the stack by this invocation, `false` if it was already
     * registered in the stack.
     */
    internal fun parkedWorkersStackPush(worker: Worker): Boolean {
        if (worker.nextParkedWorker !== NOT_IN_STACK) return false // already in stack, bail out
        /*
         * The below loop can be entered only if this worker was not in the stack and, since no other thread
         * can add it to the stack (only the worker itself), this invariant holds while this loop executes.
         */
        parkedWorkersStack.loop { top ->
            val index = (top and PARKED_INDEX_MASK).toInt()
            val updVersion = (top + PARKED_VERSION_INC) and PARKED_VERSION_MASK
            val updIndex = worker.indexInArray
            assert { updIndex != 0 } // only this worker can push itself, cannot be terminated
            worker.nextParkedWorker = workers[index]
            /*
             * Other thread can be changing this worker's index at this point, but it
             * also invokes parkedWorkersStackTopUpdate which updates version to make next CAS fail.
             * Successful CAS of the stack top completes successful push.
             */
            if (parkedWorkersStack.compareAndSet(top, updVersion or updIndex.toLong())) return true
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
     * [blockingTasks] is count of pending (either in the queue or being executed) tasks
     *
     * **NOTE**: `workers[0]` is always `null` (never used, works as sentinel value), so
     * workers are 1-indexed, code path in [Worker.trySteal] is a bit faster and index swap during termination
     * works properly
     */
    @JvmField
    val workers = AtomicReferenceArray<Worker?>(maxPoolSize + 1)

    /**
     * Long describing state of workers in this pool.
     * Currently includes created, CPU-acquired and blocking workers each occupying [BLOCKING_SHIFT] bits.
     */
    private val controlState = atomic(corePoolSize.toLong() shl CPU_PERMITS_SHIFT)
    private val createdWorkers: Int inline get() = (controlState.value and CREATED_MASK).toInt()
    private val availableCpuPermits: Int inline get() = availableCpuPermits(controlState.value)

    private inline fun createdWorkers(state: Long): Int = (state and CREATED_MASK).toInt()
    private inline fun blockingTasks(state: Long): Int = (state and BLOCKING_MASK shr BLOCKING_SHIFT).toInt()
    public inline fun availableCpuPermits(state: Long): Int = (state and CPU_PERMITS_MASK shr CPU_PERMITS_SHIFT).toInt()

    // Guarded by synchronization
    private inline fun incrementCreatedWorkers(): Int = createdWorkers(controlState.incrementAndGet())
    private inline fun decrementCreatedWorkers(): Int = createdWorkers(controlState.getAndDecrement())

    private inline fun incrementBlockingTasks() = controlState.addAndGet(1L shl BLOCKING_SHIFT)

    private inline fun decrementBlockingTasks() {
        controlState.addAndGet(-(1L shl BLOCKING_SHIFT))
    }

    private inline fun tryAcquireCpuPermit(): Boolean = controlState.loop { state ->
        val available = availableCpuPermits(state)
        if (available == 0) return false
        val update = state - (1L shl CPU_PERMITS_SHIFT)
        if (controlState.compareAndSet(state, update)) return true
    }

    private inline fun releaseCpuPermit() = controlState.addAndGet(1L shl CPU_PERMITS_SHIFT)

    // This is used a "stop signal" for close and shutdown functions
    private val _isTerminated = atomic(false)
    val isTerminated: Boolean get() = _isTerminated.value

    companion object {
        // A symbol to mark workers that are not in parkedWorkersStack
        @JvmField
        val NOT_IN_STACK = Symbol("NOT_IN_STACK")

        // Worker ctl states
        private const val PARKED = -1
        private const val CLAIMED = 0
        private const val TERMINATED = 1

        // Masks of control state
        private const val BLOCKING_SHIFT = 21 // 2M threads max
        private const val CREATED_MASK: Long = (1L shl BLOCKING_SHIFT) - 1
        private const val BLOCKING_MASK: Long = CREATED_MASK shl BLOCKING_SHIFT
        private const val CPU_PERMITS_SHIFT = BLOCKING_SHIFT * 2
        private const val CPU_PERMITS_MASK = CREATED_MASK shl CPU_PERMITS_SHIFT

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
        if (!_isTerminated.compareAndSet(false, true)) return
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
                assert { state === WorkerState.TERMINATED } // Expected TERMINATED state
                worker.localQueue.offloadAllWorkTo(globalBlockingQueue) // Doesn't actually matter which queue to use
            }
        }
        // Make sure no more work is added to GlobalQueue from anywhere
        globalBlockingQueue.close()
        globalCpuQueue.close()
        // Finish processing tasks from globalQueue and/or from this worker's local queue
        while (true) {
            val task = currentWorker?.findTask(true)
                ?: globalCpuQueue.removeFirstOrNull()
                ?: globalBlockingQueue.removeFirstOrNull()
                ?: break
            runSafely(task)
        }
        // Shutdown current thread
        currentWorker?.tryReleaseCpu(WorkerState.TERMINATED)
        // check & cleanup state
        assert { availableCpuPermits == corePoolSize }
        parkedWorkersStack.value = 0L
        controlState.value = 0L
    }

    /**
     * Dispatches execution of a runnable [block] with a hint to a scheduler whether
     * this [block] may execute blocking operations (IO, system calls, locking primitives etc.)
     *
     * [taskContext] -- concurrency context of given [block].
     * [tailDispatch] -- whether this [dispatch] call is the last action the (presumably) worker thread does in its current task.
     * If `true`, then  the task will be dispatched in a FIFO manner and no additional workers will be requested,
     * but only if the current thread is a corresponding worker thread.
     * Note that caller cannot be ensured that it is being executed on worker thread for the following reasons:
     *   * [CoroutineStart.UNDISPATCHED]
     *   * Concurrent [close] that effectively shutdowns the worker thread
     */
    fun dispatch(block: Runnable, taskContext: TaskContext = NonBlockingContext, tailDispatch: Boolean = false) {
        trackTask() // this is needed for virtual time support
        val task = createTask(block, taskContext)
        // try to submit the task to the local queue and act depending on the result
        val currentWorker = currentWorker()
        val notAdded = currentWorker.submitToLocalQueue(task, tailDispatch)
        if (notAdded != null) {
            if (!addToGlobalQueue(notAdded)) {
                // Global queue is closed in the last step of close/shutdown -- no more tasks should be accepted
                throw RejectedExecutionException("$schedulerName was terminated")
            }
        }
        val skipUnpark = tailDispatch && currentWorker != null
        // Checking 'task' instead of 'notAdded' is completely okay
        if (task.mode == TASK_NON_BLOCKING) {
            if (skipUnpark) return
            signalCpuWork()
        } else {
            // Increment blocking tasks anyway
            signalBlockingWork(skipUnpark = skipUnpark)
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

    private fun signalBlockingWork(skipUnpark: Boolean) {
        // Use state snapshot to avoid thread overprovision
        val stateSnapshot = incrementBlockingTasks()
        if (skipUnpark) return
        if (tryUnpark()) return
        if (tryCreateWorker(stateSnapshot)) return
        tryUnpark() // Try unpark again in case there was race between permit release and parking
    }

    internal fun signalCpuWork() {
        if (tryUnpark()) return
        if (tryCreateWorker()) return
        tryUnpark()
    }

    private fun tryCreateWorker(state: Long = controlState.value): Boolean {
        val created = createdWorkers(state)
        val blocking = blockingTasks(state)
        val cpuWorkers = (created - blocking).coerceAtLeast(0)
        /*
         * We check how many threads are there to handle non-blocking work,
         * and create one more if we have not enough of them.
         */
        if (cpuWorkers < corePoolSize) {
            val newCpuWorkers = createNewWorker()
            // If we've created the first cpu worker and corePoolSize > 1 then create
            // one more (second) cpu worker, so that stealing between them is operational
            if (newCpuWorkers == 1 && corePoolSize > 1) createNewWorker()
            if (newCpuWorkers > 0) return true
        }
        return false
    }

    private fun tryUnpark(): Boolean {
        while (true) {
            val worker = parkedWorkersStackPop() ?: return false
            if (worker.workerCtl.compareAndSet(PARKED, CLAIMED)) {
                LockSupport.unpark(worker)
                return true
            }
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
            val blocking = blockingTasks(state)
            val cpuWorkers = (created - blocking).coerceAtLeast(0)
            // Double check for overprovision
            if (cpuWorkers >= corePoolSize) return 0
            if (created >= maxPoolSize) return 0
            // start & register new worker, commit index only after successful creation
            val newIndex = createdWorkers + 1
            require(newIndex > 0 && workers[newIndex] == null)
            /*
             * 1) Claim the slot (under a lock) by the newly created worker
             * 2) Make it observable by increment created workers count
             * 3) Only then start the worker, otherwise it may miss its own creation
             */
            val worker = Worker(newIndex)
            workers[newIndex] = worker
            require(newIndex == incrementCreatedWorkers())
            worker.start()
            return cpuWorkers + 1
        }
    }

    /**
     * Returns `null` if task was successfully added or an instance of the
     * task that was not added or replaced (thus should be added to global queue).
     */
    private fun Worker?.submitToLocalQueue(task: Task, tailDispatch: Boolean): Task? {
        if (this == null) return task
        /*
         * This worker could have been already terminated from this thread by close/shutdown and it should not
         * accept any more tasks into its local queue.
         */
        if (state === WorkerState.TERMINATED) return task
        // Do not add CPU tasks in local queue if we are not able to execute it
        if (task.mode == TASK_NON_BLOCKING && state === WorkerState.BLOCKING) {
            return task
        }
        mayHaveLocalTasks = true
        return localQueue.add(task, fair = tailDispatch)
    }

    private fun currentWorker(): Worker? = (Thread.currentThread() as? Worker)?.takeIf { it.scheduler == this }

    /**
     * Returns a string identifying the state of this scheduler for nicer debugging.
     * Note that this method is not atomic and represents rough state of pool.
     *
     * State of the queues:
     * b for blocking, c for CPU, r for retiring.
     * E.g. for [1b, 1b, 2c, 1d] means that pool has
     * two blocking workers with queue size 1, one worker with CPU permit and queue size 1
     * and one dormant (executing his local queue before parking) worker with queue size 1.
     */
    override fun toString(): String {
        var parkedWorkers = 0
        var blockingWorkers = 0
        var cpuWorkers = 0
        var dormant = 0
        var terminated = 0
        val queueSizes = arrayListOf<String>()
        for (index in 1 until workers.length()) {
            val worker = workers[index] ?: continue
            val queueSize = worker.localQueue.size
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
                WorkerState.DORMANT -> {
                    ++dormant
                    if (queueSize > 0) queueSizes += queueSize.toString() + "d" // Retiring
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
                    "dormant = $dormant, " +
                    "terminated = $terminated}, " +
                "running workers queues = $queueSizes, "+
                "global CPU queue size = ${globalCpuQueue.size}, " +
                "global blocking queue size = ${globalBlockingQueue.size}, " +
                "Control State {" +
                    "created workers= ${createdWorkers(state)}, " +
                    "blocking tasks = ${blockingTasks(state)}, " +
                    "CPUs acquired = ${corePoolSize - availableCpuPermits(state)}" +
                "}]"
    }

    fun runSafely(task: Task) {
        try {
            task.run()
        } catch (e: Throwable) {
            val thread = Thread.currentThread()
            thread.uncaughtExceptionHandler.uncaughtException(thread, e)
        } finally {
            unTrackTask()
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

        inline val scheduler get() = this@CoroutineScheduler

        @JvmField
        val localQueue: WorkQueue = WorkQueue()

        /**
         * Worker state. **Updated only by this worker thread**.
         * By default, worker is in DORMANT state in the case when it was created, but all CPU tokens or tasks were taken.
         * Is used locally by the worker to maintain its own invariants.
         */
        @JvmField
        var state = WorkerState.DORMANT

        /**
         * Worker control state responsible for worker claiming, parking and termination.
         * List of states:
         * [PARKED] -- worker is parked and can self-terminate after a termination deadline.
         * [CLAIMED] -- worker is claimed by an external submitter.
         * [TERMINATED] -- worker is terminated and no longer usable.
         */
        val workerCtl = atomic(CLAIMED)

        /**
         * It is set to the termination deadline when started doing [park] and it reset
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

        /*
         * The delay until at least one task in other worker queues will  become stealable.
         */
        private var minDelayUntilStealableTaskNs = 0L

        private var rngState = Random.nextInt()

        /**
         * Tries to acquire CPU token if worker doesn't have one
         * @return whether worker acquired (or already had) CPU token
         */
        private fun tryAcquireCpuPermit(): Boolean = when {
            state == WorkerState.CPU_ACQUIRED -> true
            this@CoroutineScheduler.tryAcquireCpuPermit() -> {
                state = WorkerState.CPU_ACQUIRED
                true
            }
            else -> false
        }

        /**
         * Releases CPU token if worker has any and changes state to [newState].
         * Returns `true` if CPU permit was returned to the pool
         */
        internal fun tryReleaseCpu(newState: WorkerState): Boolean {
            val previousState = state
            val hadCpu = previousState == WorkerState.CPU_ACQUIRED
            if (hadCpu) releaseCpuPermit()
            if (previousState != newState) state = newState
            return hadCpu
        }

        override fun run() = runWorker()

        @JvmField
        var mayHaveLocalTasks = false

        private fun runWorker() {
            var rescanned = false
            while (!isTerminated && state != WorkerState.TERMINATED) {
                val task = findTask(mayHaveLocalTasks)
                // Task found. Execute and repeat
                if (task != null) {
                    rescanned = false
                    minDelayUntilStealableTaskNs = 0L
                    executeTask(task)
                    continue
                } else {
                    mayHaveLocalTasks = false
                }
                /*
                 * No tasks were found:
                 * 1) Either at least one of the workers has stealable task in its FIFO-buffer with a stealing deadline.
                 *    Then its deadline is stored in [minDelayUntilStealableTask]
                 *
                 * Then just park for that duration (ditto re-scanning).
                 * While it could potentially lead to short (up to WORK_STEALING_TIME_RESOLUTION_NS ns) starvations,
                 * excess unparks and managing "one unpark per signalling" invariant become unfeasible, instead we are going to resolve
                 * it with "spinning via scans" mechanism.
                 * NB: this short potential parking does not interfere with `tryUnpark`
                 */
                if (minDelayUntilStealableTaskNs != 0L) {
                    if (!rescanned) {
                        rescanned = true
                    } else {
                        rescanned = false
                        tryReleaseCpu(WorkerState.PARKING)
                        interrupted()
                        LockSupport.parkNanos(minDelayUntilStealableTaskNs)
                        minDelayUntilStealableTaskNs = 0L
                    }
                    continue
                }
                /*
                 * 2) Or no tasks available, time to park and, potentially, shut down the thread.
                 * Add itself to the stack of parked workers, re-scans all the queues
                 * to avoid missing wake-up (requestCpuWorker) and either starts executing discovered tasks or parks itself awaiting for new tasks.
                 */
                tryPark()
            }
            tryReleaseCpu(WorkerState.TERMINATED)
        }

        // Counterpart to "tryUnpark"
        private fun tryPark() {
            if (!inStack()) {
                parkedWorkersStackPush(this)
                return
            }
            assert { localQueue.size == 0 }
            workerCtl.value = PARKED // Update value once
            while (inStack()) { // Prevent spurious wakeups
                if (isTerminated || state == WorkerState.TERMINATED) break
                tryReleaseCpu(WorkerState.PARKING)
                interrupted() // Cleanup interruptions
                park()
            }
        }

        private fun inStack(): Boolean = nextParkedWorker !== NOT_IN_STACK

        private fun executeTask(task: Task) {
            val taskMode = task.mode
            idleReset(taskMode)
            beforeTask(taskMode)
            runSafely(task)
            afterTask(taskMode)
        }

        private fun beforeTask(taskMode: Int) {
            if (taskMode == TASK_NON_BLOCKING) return
            // Always notify about new work when releasing CPU-permit to execute some blocking task
            if (tryReleaseCpu(WorkerState.BLOCKING)) {
                signalCpuWork()
            }
        }

        private fun afterTask(taskMode: Int) {
            if (taskMode == TASK_NON_BLOCKING) return
            decrementBlockingTasks()
            val currentState = state
            // Shutdown sequence of blocking dispatcher
            if (currentState !== WorkerState.TERMINATED) {
                assert { currentState == WorkerState.BLOCKING } // "Expected BLOCKING state, but has $currentState"
                state = WorkerState.DORMANT
            }
        }

        /*
         * Marsaglia xorshift RNG with period 2^32-1 for work stealing purposes.
         * ThreadLocalRandom cannot be used to support Android and ThreadLocal<Random> is up to 15% slower on Ktor benchmarks
         */
        internal fun nextInt(upperBound: Int): Int {
            var r = rngState
            r = r xor (r shl 13)
            r = r xor (r shr 17)
            r = r xor (r shl 5)
            rngState = r
            val mask = upperBound - 1
            // Fast path for power of two bound
            if (mask and upperBound == 0) {
                return r and mask
            }
            return (r and Int.MAX_VALUE) % upperBound
        }

        private fun park() {
            // set termination deadline the first time we are here (it is reset in idleReset)
            if (terminationDeadline == 0L) terminationDeadline = System.nanoTime() + idleWorkerKeepAliveNs
            // actually park
            LockSupport.parkNanos(idleWorkerKeepAliveNs)
            // try terminate when we are idle past termination deadline
            // note that comparison is written like this to protect against potential nanoTime wraparound
            if (System.nanoTime() - terminationDeadline >= 0) {
                terminationDeadline = 0L // if attempt to terminate worker fails we'd extend deadline again
                tryTerminateWorker()
            }
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
                /*
                 * See tryUnpark for state reasoning.
                 * If this CAS fails, then we were successfully unparked by other worker and cannot terminate.
                 */
                if (!workerCtl.compareAndSet(PARKED, TERMINATED)) return
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

        // It is invoked by this worker when it finds a task
        private fun idleReset(mode: Int) {
            terminationDeadline = 0L // reset deadline for termination
            if (state == WorkerState.PARKING) {
                assert { mode == TASK_PROBABLY_BLOCKING }
                state = WorkerState.BLOCKING
            }
        }

        fun findTask(scanLocalQueue: Boolean): Task? {
            if (tryAcquireCpuPermit()) return findAnyTask(scanLocalQueue)
            // If we can't acquire a CPU permit -- attempt to find blocking task
            val task = if (scanLocalQueue) {
                localQueue.poll() ?: globalBlockingQueue.removeFirstOrNull()
            } else {
                globalBlockingQueue.removeFirstOrNull()
            }
            return task ?: trySteal(blockingOnly = true)
        }

        private fun findAnyTask(scanLocalQueue: Boolean): Task? {
            /*
             * Anti-starvation mechanism: probabilistically poll either local
             * or global queue to ensure progress for both external and internal tasks.
             */
            if (scanLocalQueue) {
                val globalFirst = nextInt(2 * corePoolSize) == 0
                if (globalFirst) pollGlobalQueues()?.let { return it }
                localQueue.poll()?.let { return it }
                if (!globalFirst) pollGlobalQueues()?.let { return it }
            } else {
                pollGlobalQueues()?.let { return it }
            }
            return trySteal(blockingOnly = false)
        }

        private fun pollGlobalQueues(): Task? {
            if (nextInt(2) == 0) {
                globalCpuQueue.removeFirstOrNull()?.let { return it }
                return globalBlockingQueue.removeFirstOrNull()
            } else {
                globalBlockingQueue.removeFirstOrNull()?.let { return it }
                return globalCpuQueue.removeFirstOrNull()
            }
        }

        private fun trySteal(blockingOnly: Boolean): Task? {
            assert { localQueue.size == 0 }
            val created = createdWorkers
            // 0 to await an initialization and 1 to avoid excess stealing on single-core machines
            if (created < 2) {
                return null
            }

            var currentIndex = nextInt(created)
            var minDelay = Long.MAX_VALUE
            repeat(created) {
                ++currentIndex
                if (currentIndex > created) currentIndex = 1
                val worker = workers[currentIndex]
                if (worker !== null && worker !== this) {
                    assert { localQueue.size == 0 }
                    val stealResult = if (blockingOnly) {
                        localQueue.tryStealBlockingFrom(victim = worker.localQueue)
                    } else {
                        localQueue.tryStealFrom(victim = worker.localQueue)
                    }
                    if (stealResult == TASK_STOLEN) {
                        return localQueue.poll()
                    } else if (stealResult > 0) {
                        minDelay = min(minDelay, stealResult)
                    }
                }
            }
            minDelayUntilStealableTaskNs = if (minDelay != Long.MAX_VALUE) minDelay else 0
            return null
        }
    }

    enum class WorkerState {
        /**
         * Has CPU token and either executes [TASK_NON_BLOCKING] task or tries to find one.
         */
        CPU_ACQUIRED,

        /**
         * Executing task with [TASK_PROBABLY_BLOCKING].
         */
        BLOCKING,

        /**
         * Currently parked.
         */
        PARKING,

        /**
         * Tries to execute its local work and then goes to infinite sleep as no longer needed worker.
         */
        DORMANT,

        /**
         * Terminal state, will no longer be used
         */
        TERMINATED
    }
}
