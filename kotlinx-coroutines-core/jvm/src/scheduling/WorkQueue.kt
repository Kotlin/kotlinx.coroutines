package kotlinx.coroutines.scheduling

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import java.util.concurrent.atomic.*
import kotlin.jvm.internal.Ref.ObjectRef

internal const val BUFFER_CAPACITY_BASE = 7
internal const val BUFFER_CAPACITY = 1 shl BUFFER_CAPACITY_BASE
internal const val MASK = BUFFER_CAPACITY - 1 // 128 by default

internal const val TASK_STOLEN = -1L
internal const val NOTHING_TO_STEAL = -2L

internal typealias StealingMode = Int
internal const val STEAL_ANY: StealingMode = 3
internal const val STEAL_CPU_ONLY: StealingMode = 2
internal const val STEAL_BLOCKING_ONLY: StealingMode = 1

internal inline val Task.maskForStealingMode: Int
    get() = if (isBlocking) STEAL_BLOCKING_ONLY else STEAL_CPU_ONLY

/**
 * Tightly coupled with [CoroutineScheduler] queue of pending tasks, but extracted to separate file for simplicity.
 * At any moment queue is used only by [CoroutineScheduler.Worker] threads, has only one producer (worker owning this queue)
 * and any amount of consumers, other pool workers which are trying to steal work.
 *
 * ### Fairness
 *
 * [WorkQueue] provides semi-FIFO order, but with priority for most recently submitted task assuming
 * that these two (current one and submitted) are communicating and sharing state thus making such communication extremely fast.
 * E.g. submitted jobs [1, 2, 3, 4] will be executed in [4, 1, 2, 3] order.
 *
 * ### Algorithm and implementation details
 * This is a regular SPMC bounded queue with the additional property that tasks can be removed from the middle of the queue
 * (scheduler workers without a CPU permit steal blocking tasks via this mechanism). Such property enforces us to use CAS in
 * order to properly claim value from the buffer.
 * Moreover, [Task] objects are reusable, so it may seem that this queue is prone to ABA problem.
 * Indeed, it formally has ABA-problem, but the whole processing logic is written in the way that such ABA is harmless.
 * I have discovered a truly marvelous proof of this, which this KDoc is too narrow to contain.
 */
internal class WorkQueue {

    /*
     * We read two independent counter here.
     * Producer index is incremented only by owner
     * Consumer index is incremented both by owner and external threads
     *
     * The only harmful race is:
     * [T1] readProducerIndex (1) preemption(2) readConsumerIndex(5)
     * [T2] changeProducerIndex (3)
     * [T3] changeConsumerIndex (4)
     *
     * Which can lead to resulting size being negative or bigger than actual size at any moment of time.
     * This is in general harmless because steal will be blocked by timer.
     * Negative sizes can be observed only when non-owner reads the size, which happens only
     * for diagnostic toString().
     */
    private val bufferSize: Int get() = producerIndex.value - consumerIndex.value
    internal val size: Int get() = if (lastScheduledTask.value != null) bufferSize + 1 else bufferSize
    private val buffer: AtomicReferenceArray<Task?> = AtomicReferenceArray(BUFFER_CAPACITY)
    private val lastScheduledTask = atomic<Task?>(null)

    private val producerIndex = atomic(0)
    private val consumerIndex = atomic(0)
    // Shortcut to avoid scanning queue without blocking tasks
    private val blockingTasksInBuffer = atomic(0)

    /**
     * Retrieves and removes task from the head of the queue
     * Invariant: this method is called only by the owner of the queue.
     */
    fun poll(): Task? = lastScheduledTask.getAndSet(null) ?: pollBuffer()

    /**
     * Invariant: Called only by the owner of the queue, returns
     * `null` if task was added, task that wasn't added otherwise.
     */
    fun add(task: Task, fair: Boolean = false): Task? {
        if (fair) return addLast(task)
        val previous = lastScheduledTask.getAndSet(task) ?: return null
        return addLast(previous)
    }

    /**
     * Invariant: Called only by the owner of the queue, returns
     * `null` if task was added, task that wasn't added otherwise.
     */
    private fun addLast(task: Task): Task? {
        if (bufferSize == BUFFER_CAPACITY - 1) return task
        if (task.isBlocking) blockingTasksInBuffer.incrementAndGet()
        val nextIndex = producerIndex.value and MASK
        /*
         * If current element is not null then we're racing with a really slow consumer that committed the consumer index,
         * but hasn't yet nulled out the slot, effectively preventing us from using it.
         * Such situations are very rare in practise (although possible) and we decided to give up a progress guarantee
         * to have a stronger invariant "add to queue with bufferSize == 0 is always successful".
         * This algorithm can still be wait-free for add, but if and only if tasks are not reusable, otherwise
         * nulling out the buffer wouldn't be possible.
         */
        while (buffer[nextIndex] != null) {
            Thread.yield()
        }
        buffer.lazySet(nextIndex, task)
        producerIndex.incrementAndGet()
        return null
    }

    /**
     * Tries stealing from this queue into the [stolenTaskRef] argument.
     *
     * Returns [NOTHING_TO_STEAL] if queue has nothing to steal, [TASK_STOLEN] if at least task was stolen
     * or positive value of how many nanoseconds should pass until the head of this queue will be available to steal.
     *
     * [StealingMode] controls what tasks to steal:
     * - [STEAL_ANY] is default mode for scheduler, task from the head (in FIFO order) is stolen
     * - [STEAL_BLOCKING_ONLY] is mode for stealing *an arbitrary* blocking task, which is used by the scheduler when helping in Dispatchers.IO mode
     * - [STEAL_CPU_ONLY] is a kludge for `runSingleTaskFromCurrentSystemDispatcher`
     */
    fun trySteal(stealingMode: StealingMode, stolenTaskRef: ObjectRef<Task?>): Long {
        val task = when (stealingMode) {
            STEAL_ANY -> pollBuffer()
            else -> stealWithExclusiveMode(stealingMode)
        }

        if (task != null) {
            stolenTaskRef.element = task
            return TASK_STOLEN
        }
        return tryStealLastScheduled(stealingMode, stolenTaskRef)
    }

    // Steal only tasks of a particular kind, potentially invoking full queue scan
    private fun stealWithExclusiveMode(stealingMode: StealingMode): Task? {
        var start = consumerIndex.value
        val end = producerIndex.value
        val onlyBlocking = stealingMode == STEAL_BLOCKING_ONLY
        // Bail out if there is no blocking work for us
        while (start != end) {
            if (onlyBlocking && blockingTasksInBuffer.value == 0) return null
            return tryExtractFromTheMiddle(start++, onlyBlocking) ?: continue
        }

        return null
    }

    // Polls for blocking task, invoked only by the owner
    // NB: ONLY for runSingleTask method
    fun pollBlocking(): Task? = pollWithExclusiveMode(onlyBlocking = true /* only blocking */)

    // Polls for CPU task, invoked only by the owner
    // NB: ONLY for runSingleTask method
    fun pollCpu(): Task? = pollWithExclusiveMode(onlyBlocking = false /* only cpu */)

    private fun pollWithExclusiveMode(/* Only blocking OR only CPU */ onlyBlocking: Boolean): Task? {
        while (true) { // Poll the slot
            val lastScheduled = lastScheduledTask.value ?: break
            if (lastScheduled.isBlocking != onlyBlocking) break
            if (lastScheduledTask.compareAndSet(lastScheduled, null)) {
                return lastScheduled
            } // Failed -> someone else stole it
        }

        // Failed to poll the slot, scan the queue
        val start = consumerIndex.value
        var end = producerIndex.value
        // Bail out if there is no blocking work for us
        while (start != end) {
            if (onlyBlocking && blockingTasksInBuffer.value == 0) return null
            val task = tryExtractFromTheMiddle(--end, onlyBlocking)
            if (task != null) {
                return task
            }
        }
        return null
    }

    private fun tryExtractFromTheMiddle(index: Int, onlyBlocking: Boolean): Task? {
        val arrayIndex = index and MASK
        val value = buffer[arrayIndex]
        if (value != null && value.isBlocking == onlyBlocking && buffer.compareAndSet(arrayIndex, value, null)) {
            if (onlyBlocking) blockingTasksInBuffer.decrementAndGet()
            return value
        }
        return null
    }

    fun offloadAllWorkTo(globalQueue: GlobalQueue) {
        lastScheduledTask.getAndSet(null)?.let { globalQueue.addLast(it) }
        while (pollTo(globalQueue)) {
            // Steal everything
        }
    }

    /**
     * Contract on return value is the same as for [trySteal]
     */
    private fun tryStealLastScheduled(stealingMode: StealingMode, stolenTaskRef: ObjectRef<Task?>): Long {
        while (true) {
            val lastScheduled = lastScheduledTask.value ?: return NOTHING_TO_STEAL
            if ((lastScheduled.maskForStealingMode and stealingMode) == 0) {
                return NOTHING_TO_STEAL
            }

            // TODO time wraparound ?
            val time = schedulerTimeSource.nanoTime()
            val staleness = time - lastScheduled.submissionTime
            if (staleness < WORK_STEALING_TIME_RESOLUTION_NS) {
                return WORK_STEALING_TIME_RESOLUTION_NS - staleness
            }

            /*
             * If CAS has failed, either someone else had stolen this task or the owner executed this task
             * and dispatched another one. In the latter case we should retry to avoid missing task.
             */
            if (lastScheduledTask.compareAndSet(lastScheduled, null)) {
                stolenTaskRef.element = lastScheduled
                return TASK_STOLEN
            }
            continue
        }
    }

    private fun pollTo(queue: GlobalQueue): Boolean {
        val task = pollBuffer() ?: return false
        queue.addLast(task)
        return true
    }

    private fun pollBuffer(): Task? {
        while (true) {
            val tailLocal = consumerIndex.value
            if (tailLocal - producerIndex.value == 0) return null
            val index = tailLocal and MASK
            if (consumerIndex.compareAndSet(tailLocal, tailLocal + 1)) {
                // Nulls are allowed when blocking tasks are stolen from the middle of the queue.
                val value = buffer.getAndSet(index, null) ?: continue
                value.decrementIfBlocking()
                return value
            }
        }
    }

    private fun Task?.decrementIfBlocking() {
        if (this != null && isBlocking) {
            val value = blockingTasksInBuffer.decrementAndGet()
            assert { value >= 0 }
        }
    }
}
