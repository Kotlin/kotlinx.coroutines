package kotlinx.coroutines.experimental.scheduling

import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicReference
import java.util.concurrent.atomic.AtomicReferenceArray

internal const val BUFFER_CAPACITY_BASE = 7
internal const val BUFFER_CAPACITY = 1 shl BUFFER_CAPACITY_BASE
internal const val MASK = BUFFER_CAPACITY - 1 // 128 by default

/**
 * Unstable API and subject to change.
 * Tightly coupled with [CoroutineScheduler] queue of pending tasks, but extracted to separate file for simplicity.
 * At any moment queue is used only by [CoroutineScheduler.PoolWorker] threads, has only one producer (worker owning this queue)
 * and any amount of consumers, other pool workers which are trying to steal work.
 *
 * Fairness
 * [WorkQueue] provides semi-FIFO order, but with priority for most recently submitted task assuming
 * that these two (current and submitted) are communicating and sharing state thus making such communication extremely fast.
 * E.g. submitted jobs [1, 2, 3, 4] will be executed in [4, 1, 2, 3] order.
 *
 * Work offloading
 * When queue is full, half of existing tasks is offloaded to global queue which is regularly polled by other pool workers.
 * Offloading occurs in LIFO order for the sake of implementation simplicity: offload should be extremely rare and occurs only in specific use-cases
 * (e.g. when coroutine starts heavy fork-join-like computation), so fairness is not important.
 * As an alternative, offloading directly to some [CoroutineScheduler.PoolWorker] may be used, but then strategy of selecting most idle worker
 * should be implemented and implementation should be aware multiple producers.
 */
internal class WorkQueue {

    internal val bufferSize: Int get() = producerIndex.get() - consumerIndex.get()
    private val buffer: AtomicReferenceArray<Task?> = AtomicReferenceArray(BUFFER_CAPACITY)
    private val lastScheduledTask: AtomicReference<Task?> = AtomicReference(null)

    private val producerIndex: AtomicInteger = AtomicInteger(0)
    private val consumerIndex: AtomicInteger = AtomicInteger(0)

    /**
     * Retrieves and removes task from head of the queue
     * Invariant: this method is called only by owner of the queue ([pollExternal] is not)
     */
    fun poll(): Task? {
        return lastScheduledTask.getAndSet(null) ?: pollExternal()
    }

    /**
     * Invariant: this method is called only by owner of the queue
     * @param task task to put into local queue
     * @param globalQueue fallback queue which is used when local queue is overflown
     */
    fun offer(task: Task, globalQueue: GlobalQueue) {
        while (true) {
            val previous = lastScheduledTask.get()
            if (lastScheduledTask.compareAndSet(previous, task)) {
                if (previous != null) {
                    addLast(previous, globalQueue)
                }
                return
            }
        }
    }

    /**
     * Offloads half of the current buffer to [sink]
     * @param byTimer whether task deadline should be checked before offloading
     */
    inline fun offloadWork(byTimer: Boolean, sink: (Task) -> Unit) {
        repeat((bufferSize / 2).coerceAtLeast(1)) {
            if (bufferSize == 0) { // try to steal head if buffer is empty
                val lastScheduled = lastScheduledTask.get() ?: return
                if (!byTimer || schedulerTimeSource.nanoTime() - lastScheduled.submissionTime < WORK_STEALING_TIME_RESOLUTION) {
                    return
                }

                if (lastScheduledTask.compareAndSet(lastScheduled, null)) {
                    sink(lastScheduled)
                    return
                }
            }

            // TODO use batch drain and (if target queue allows) batch insert
            val task = pollExternal { !byTimer || schedulerTimeSource.nanoTime() - it.submissionTime >= WORK_STEALING_TIME_RESOLUTION }
                    ?: return
            sink(task)
        }
    }

    /**
     * [poll] for external (not owning this queue) workers
     */
    private inline fun pollExternal(predicate: (Task) -> Boolean = { true }): Task? {
        while (true) {
            val tailLocal = consumerIndex.get()
            if (tailLocal - producerIndex.get() == 0) return null
            val index = tailLocal and MASK
            val element = buffer[index] ?: continue
            if (!predicate(element)) {
                return null
            }

            if (consumerIndex.compareAndSet(tailLocal, tailLocal + 1)) {
                // 1) Help GC 2) Signal producer that this slot is consumed and may be used
                return buffer.getAndSet(index, null)
            }
        }
    }

    // Called only by owner
    private fun addLast(task: Task, globalQueue: GlobalQueue) {
        while (!tryAddLast(task)) {
            offloadWork(false) {
                globalQueue.add(it)
            }
        }
    }

    // Called only by owner
    private fun tryAddLast(task: Task): Boolean {
        if (bufferSize == BUFFER_CAPACITY - 1) return false
        val headLocal = producerIndex.get()
        val nextIndex = headLocal and MASK

        /*
         * If current element is not null then we're racing with consumers for tail. If we skip this check then
         * consumer can null out current element and it will be lost. If we're racing for tail then
         * queue is close to overflow => it's fine to offload work to global queue
         */
        if (buffer[nextIndex] != null) {
            return false
        }

        buffer.lazySet(nextIndex, task)
        producerIndex.incrementAndGet()
        return true
    }
}
