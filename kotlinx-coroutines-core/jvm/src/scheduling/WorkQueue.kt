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

internal const val TASK_STOLEN = -1L
internal const val NOTHING_TO_STEAL = -2L

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
    internal val size: Int get() = if (lastScheduledTask.value != null) bufferSize + 1 else bufferSize
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
     * Invariant: Called only by the owner of the queue, returns
     * `null` if task was added, task that wasn't added otherwise.
     */
    fun add(task: Task): Task? {
        val previous = lastScheduledTask.getAndSet(task) ?: return null
        return addLast(previous)
    }

    /**
     * Invariant: Called only by the owner of the queue, returns
     * `null` if task was added, task that wasn't added otherwise.
     */
    fun addLast(task: Task): Task? {
        if (bufferSize == BUFFER_CAPACITY - 1) return task
        val headLocal = producerIndex.value
        val nextIndex = headLocal and MASK

        /*
         * If current element is not null then we're racing with consumers for the tail. If we skip this check then
         * the consumer can null out current element and it will be lost. If we're racing for tail then
         * the queue is close to overflowing => return task
         */
        if (buffer[nextIndex] != null) {
            return task
        }
        buffer.lazySet(nextIndex, task)
        producerIndex.incrementAndGet()
        return null
    }

    /**
     * Tries stealing from [victim] queue into this queue.
     *
     * Returns [NOTHING_TO_STEAL] if queue has nothing to steal, [TASK_STOLEN] if at least task was stolen
     * or positive value of how many nanoseconds should pass until the head of this queue will be available to steal.
     */
    fun tryStealFrom(victim: WorkQueue): Long {
        if (victim.stealBatch { task -> add(task) }) {
            return TASK_STOLEN
        }
        return tryStealLastScheduled(victim)
    }

    /**
     * Contract on return value is the same as for [tryStealFrom]
     */
    private fun tryStealLastScheduled(victim: WorkQueue): Long {
        while (true) {
            val lastScheduled = victim.lastScheduledTask.value ?: return NOTHING_TO_STEAL
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
            if (victim.lastScheduledTask.compareAndSet(lastScheduled, null)) {
                add(lastScheduled)
                return TASK_STOLEN
            }
            continue
        }
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
            if (tailLocal - producerIndex.value == 0) return wasStolen
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
}
