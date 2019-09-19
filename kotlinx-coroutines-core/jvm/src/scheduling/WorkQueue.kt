/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import java.util.concurrent.atomic.*

internal const val BUFFER_CAPACITY_BASE = 7
internal const val BUFFER_CAPACITY = 1 shl BUFFER_CAPACITY_BASE
internal const val MASK = BUFFER_CAPACITY - 1 // 128 by default

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
 * ### Work offloading
 * 
 * When the queue is full, half of existing tasks are offloaded to global queue which is regularly polled by other pool workers.
 * Offloading occurs in LIFO order for the sake of implementation simplicity: offloads should be extremely rare and occurs only in specific use-cases
 * (e.g. when coroutine starts heavy fork-join-like computation), so fairness is not important.
 * As an alternative, offloading directly to some [CoroutineScheduler.Worker] may be used, but then the strategy of selecting any idle worker
 * should be implemented and implementation should be aware multiple producers.
 *
 * @suppress **This is unstable API and it is subject to change.**
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
     * Which can lead to resulting size bigger than actual size at any moment of time.
     * This is in general harmless because steal will be blocked by timer
     */
    internal val bufferSize: Int get() = producerIndex.value - consumerIndex.value

    // TODO replace with inlined array when atomicfu will support it
    private val buffer: AtomicReferenceArray<Task?> = AtomicReferenceArray(BUFFER_CAPACITY)

    private val lastScheduledTask = atomic<Task?>(null)

    private val producerIndex = atomic(0)
    private val consumerIndex = atomic(0)

    /**
     * Retrieves and removes task from the head of the queue
     * Invariant: this method is called only by the owner of the queue ([stealBatch] is not)
     */
    fun poll(): Task? = lastScheduledTask.getAndSet(null) ?: pollBuffer()

    /**
     * Invariant: this method is called only by the owner of the queue
     *
     * @param task task to put into local queue
     * @param globalQueue fallback queue which is used when the local queue is overflown
     * @return true if no offloading happened, false otherwise
     */
    fun add(task: Task, globalQueue: GlobalQueue): Boolean {
        val previous = lastScheduledTask.getAndSet(task) ?: return true
        return addLast(previous, globalQueue)
    }

    // Called only by the owner, returns true if no offloading happened, false otherwise
    fun addLast(task: Task, globalQueue: GlobalQueue): Boolean {
        var noOffloadingHappened = true
        /*
         * We need the loop here because race possible not only on full queue,
         * but also on queue with one element during stealing
         */
        while (!tryAddLast(task)) {
            offloadWork(globalQueue)
            noOffloadingHappened = false
        }
        return noOffloadingHappened
    }

    /**
     * Tries stealing from [victim] queue into this queue, using [globalQueue] to offload stolen tasks in case of current queue overflow.
     *
     * @return whether any task was stolen
     */
    fun trySteal(victim: WorkQueue, globalQueue: GlobalQueue): Boolean {
        if (victim.stealBatch { task -> add(task, globalQueue) }) {
            return true
        }
        return tryStealLastScheduled(victim, globalQueue)
    }

    private fun tryStealLastScheduled(
        victim: WorkQueue,
        globalQueue: GlobalQueue
    ): Boolean {
        val lastScheduled = victim.lastScheduledTask.value ?: return false
        val time = schedulerTimeSource.nanoTime()
        if (time - lastScheduled.submissionTime < WORK_STEALING_TIME_RESOLUTION_NS) {
            return false
        }

        if (victim.lastScheduledTask.compareAndSet(lastScheduled, null)) {
            add(lastScheduled, globalQueue)
            return true
        }
        return false
    }

    internal fun size(): Int = if (lastScheduledTask.value != null) bufferSize + 1 else bufferSize

    /**
     * Offloads half of the current buffer to [globalQueue]
     */
    private fun offloadWork(globalQueue: GlobalQueue) {
        stealBatchTo(globalQueue)
    }

    private fun GlobalQueue.add(task: Task) {
        /*
         * globalQueue is closed as the very last step in the shutdown sequence when all worker threads had
         * been already shutdown (with the only exception of the last worker thread that might be performing
         * shutdown procedure itself). As a consistency check we do a [cheap!] check that it is not closed here yet.
         */
        val added = addLast(task)
        assert { added }
    }

    internal fun offloadAllWork(globalQueue: GlobalQueue) {
        lastScheduledTask.getAndSet(null)?.let { globalQueue.add(it) }
        while (stealBatchTo(globalQueue)) {
            // Steal everything
        }
    }

    /**
     * Method that is invoked by external workers to steal work.
     * Half of the buffer (at least 1) is stolen, returns `true` if at least one task was stolen.
     */
    private inline fun stealBatch(consumer: (Task) -> Unit): Boolean {
        val size = bufferSize
        if (size == 0) return false
        var toSteal = (size / 2).coerceAtLeast(1)
        var wasStolen = false
        while (toSteal-- > 0) {
            val tailLocal = consumerIndex.value
            if (tailLocal - producerIndex.value == 0) return false
            val index = tailLocal and MASK
            val element = buffer[index] ?: continue
            if (consumerIndex.compareAndSet(tailLocal, tailLocal + 1)) {
                // 1) Help GC 2) Signal producer that this slot is consumed and may be used
                consumer(element)
                buffer[index] = null
                wasStolen = true
            }
        }
        return wasStolen
    }

    private fun stealBatchTo(queue: GlobalQueue): Boolean {
        return stealBatch { queue.add(it) }
    }

    private fun pollBuffer(): Task? {
        while (true) {
            val tailLocal = consumerIndex.value
            if (tailLocal - producerIndex.value == 0) return null
            val index = tailLocal and MASK
            if (consumerIndex.compareAndSet(tailLocal, tailLocal + 1)) {
                return buffer.getAndSet(index, null)
            }
        }
    }

    // Called only by the owner
    private fun tryAddLast(task: Task): Boolean {
        if (bufferSize == BUFFER_CAPACITY - 1) return false
        val headLocal = producerIndex.value
        val nextIndex = headLocal and MASK

        /*
         * If current element is not null then we're racing with consumers for the tail. If we skip this check then
         * the consumer can null out current element and it will be lost. If we're racing for tail then
         * the queue is close to overflowing => it's fine to offload work to global queue
         */
        if (buffer[nextIndex] != null) {
            return false
        }

        buffer.lazySet(nextIndex, task)
        producerIndex.incrementAndGet()
        return true
    }
}
