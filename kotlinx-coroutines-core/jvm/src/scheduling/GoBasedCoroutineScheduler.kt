/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.atomicfu.*
import kotlinx.atomicfu.AtomicBoolean
import kotlinx.coroutines.internal.*
import java.io.*
import java.lang.Runnable
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import java.util.concurrent.locks.*
import java.util.concurrent.locks.ReentrantLock
import kotlin.random.*

internal class GoBasedCoroutineScheduler(
    val nProcessors: Int
) : Executor, Closeable {
    val processors: List<Processor> = (0 until nProcessors).map { Processor() }
    val globalQueue = ConcurrentLinkedQueue<Task>()
    val globalLock = ReentrantLock()

    val nIdleProcessors: AtomicInt = atomic(nProcessors)
    val idleProcessor: AtomicRef<Processor?> = atomic(processors[0])

    val nSpinningWorkers: AtomicInt = atomic(0)

    val randomOrderCoprimes: List<Int>

    init {
        processors.forEachIndexed { index, processor ->
            processor.nextProcessor.value = processors.getOrNull(index + 1)
        }
        val coprimes = mutableListOf<Int>()
        for (i in 1..nProcessors) {
            if (gcd(nProcessors, i) == 1) {
                coprimes.add(i)
            }
        }
        randomOrderCoprimes = coprimes
    }

    private fun gcd(a: Int, b: Int): Int {
        var aa = a
        var bb = b
        while (bb != 0) {
            val rem = aa % bb
            aa = bb
            bb = rem
        }
        return aa
    }

    fun dispatch(block: Runnable, taskContext: TaskContext = NonBlockingContext, tailDispatch: Boolean = false) {
        val task = createTask(block, taskContext)
        val currentWorker = currentWorker()
        val notAdded = currentWorker.submitToLocalQueue(task, tailDispatch)
        if (notAdded != null) {
            addToGlobalQueue(notAdded)
        }
        wakeProcessorIfNeeded()
    }

    private fun wakeProcessorIfNeeded() {
        // todo: check spinning
        if (nIdleProcessors.value > 0) {
            startWorker(null)
        }
    }

    // done until spinning impl
    private fun startWorker(p: Processor?) {
        globalLock.lock()
        val processor = p
            ?: acquireIdleProcessor()
            ?: run {
                globalLock.unlock()
                return
            }
        val idleWorker = getIdleWorker()
        if (idleWorker == null) {
            globalLock.unlock()
            createWorker(processor)
            return
        }
        wakeupIdleWorker(processor)
        globalLock.unlock()
    }

    private fun createWorker(processor: Processor) {
        val worker = Worker(processor)
        processor.worker.value = worker
        processor.status.value = ProcessorStatus.RUNNING
        worker.start()
    }

    private fun wakeupIdleWorker(processor: Processor) {
        TODO("Not yet implemented")
    }

    // todo: check if it is applicable in jvm
    private fun getIdleWorker(): Worker? {
        // todo: implement
        return null
    }

    // sched.lock must be held
    private fun acquireIdleProcessor(): Processor? {
        assert(globalLock.isHeldByCurrentThread)

        return idleProcessor.value?.also {
            idleProcessor.value = it.nextProcessor.value
            nIdleProcessors.decrementAndGet()
        }
    }

    private fun addToGlobalQueue(task: Task): Boolean {
        return globalQueue.add(task)
    }

    //similar to getg().m but nullable
    private fun currentWorker(): Worker? =
        (Thread.currentThread() as? Worker)?.takeIf { it.scheduler == this }

    private fun Worker?.submitToLocalQueue(task: Task, tailDispatch: Boolean): Task? {
        if (this == null) return task

        val processor = this.processor.value ?: return task

        processor.queue.add(task)

        return null
    }

    fun createTask(block: Runnable, taskContext: TaskContext): Task {
        val nanoTime = schedulerTimeSource.nanoTime()
        if (block is Task) {
            block.submissionTime = nanoTime
            block.taskContext = taskContext
            return block
        }
        return TaskImpl(block, nanoTime, taskContext)
    }

    internal inner class Processor {
        internal val queue = ProcessorWorkQueue()
        internal val scheduleTick = atomic(0L)
        internal val worker: AtomicRef<Worker?> = atomic(null)
        internal val status: AtomicRef<ProcessorStatus> = atomic(ProcessorStatus.IDLE)
        internal val nextProcessor: AtomicRef<Processor?> = atomic(null)
        internal val queueLock = atomic(false)

        internal inner class ProcessorWorkQueue {
            internal val bufferSize: Int get() = producerIndex.value - consumerIndex.value
            internal val size: Int get() = if (lastScheduledTask.value != null) bufferSize + 1 else bufferSize
            private val buffer: AtomicReferenceArray<Task?> = AtomicReferenceArray(BUFFER_CAPACITY)
            private val lastScheduledTask = atomic<Task?>(null)

            private val producerIndex = atomic(0)
            private val consumerIndex = atomic(0)

            fun poll(): Task? = lastScheduledTask.getAndSet(null) ?: pollBuffer()

            private fun pollBuffer(): Task? {
                while (true) {
                    val headLocal = consumerIndex.value
                    if (headLocal - producerIndex.value == 0) return null
                    val index = headLocal and MASK
                    if (consumerIndex.compareAndSet(headLocal, headLocal + 1)) {
                        return buffer.getAndSet(index, null) ?: continue
                    }
                }
            }

            fun add(task: Task, fair: Boolean = false) {
                if (!fair) {
                    val previous = lastScheduledTask.getAndSet(task) ?: return
                    addToBuffer(previous)
                    return
                }
                addToBuffer(task)
            }

            private fun addToBuffer(task: Task) {
                while (true) {
                    val head = consumerIndex.value
                    val tail = producerIndex.value
                    if (tail % 64 == 1) {
                        run { }
                    }
                    if (tail - head < BUFFER_CAPACITY) {
                        val nextIndex = tail and MASK
                        /*
                         * If current element is not null then we're racing with a really slow consumer that committed the consumer index,
                         * but hasn't yet nulled out the slot, effectively preventing us from using it.
                         * Such situations are very rare in practise (although possible) and we decided to give up a progress guarantee
                         * to have a stronger invariant "add to queue with bufferSize == 0 is always successful".
                         * This algorithm can still be wait-free for add, but if and only if tasks are not reusable, otherwise
                         * nulling out the buffer wouldn't be possible.
                         */
                        // todo: is it really needed?
//                        while (buffer[nextIndex] != null) {
//                            Thread.yield()
//                        }
                        buffer.set(nextIndex, task)
                        producerIndex.incrementAndGet()
                        return
                    }
//                    return

                    if (addToGlobal(task, head, tail)) {
                        return
                    } else {
                        run {}
                    }
                }
            }

            private fun addToGlobal(task: Task, head: Int, tail: Int): Boolean {
                val n = (tail - head) / 2
                if (n != BUFFER_CAPACITY / 2) {
                    throw IllegalStateException("queue is not full")
                }
                val batchToMove = mutableListOf<Task>()
                for (i in 0 until n) {
                    val curTask = buffer[(head + i) and MASK] ?: return false
                    batchToMove.add(curTask)
                }
                if (!consumerIndex.compareAndSet(head, head + n)) return false
                batchToMove.add(task)

                globalLock.withLock {
                    moveToGlobal(batchToMove)
                }
                return true
            }

            // todo: better global queue
            private fun moveToGlobal(batchToMove: MutableList<Task>) {
                globalQueue.addAll(batchToMove)
            }

            fun tryStealFrom(queue: ProcessorWorkQueue, stealLastScheduled: Boolean): Task? {
                val tail = producerIndex.value
                var n = tryGrabFrom(queue, tail, stealLastScheduled)
                if (n == 0) {
                    return null
                }
                n--
                val task = buffer.getAndSet((tail + n) and MASK, null)
                producerIndex.value = tail + n
                return task
            }

            private fun tryGrabFrom(queue: ProcessorWorkQueue, batchStart: Int, stealLastScheduled: Boolean): Int {
                while (true) {
                    val head = queue.consumerIndex.value
                    val tail = queue.producerIndex.value
                    val n = (tail - head + 1) / 2
                    if (n == 0) {
                        if (stealLastScheduled) {
                            val stolen = queue.lastScheduledTask.getAndSet(null)
                            if (stolen != null) {
                                buffer[batchStart and MASK] = stolen
                                return 1
                            }
                        }
                        return 0
                    }
                    if (n > BUFFER_CAPACITY / 2) {
                        continue
                    }
                    for (i in 0 until n) {
                        val stolen = queue.buffer[(head + i) and MASK]
                        buffer[(batchStart + i) and MASK] = stolen
                    }
                    if (queue.consumerIndex.compareAndSet(head, head + n)) {
                        return n
                    }
                }
            }
        }
    }

    internal enum class ProcessorStatus {
        IDLE, RUNNING
    }

    // todo: find if worker locks needed
    // todo: rewrite
    internal inner class Worker constructor(
        processor: Processor?,
        val spinning: AtomicBoolean = atomic(false),
    ) : Thread() {
        internal val processor: AtomicRef<Processor?> = atomic(processor)

        init {
            isDaemon = true
        }

        inline val scheduler get() = this@GoBasedCoroutineScheduler

        private var rngState = Random.nextInt()

        override fun run() = runWorker()

        private fun runWorker() {
            val p = processor.value ?: throw IllegalStateException("worker runs without a processor")
            while (true) {

                if (p.scheduleTick.value % 61 == 0L) {
                    val taskFromGlobalQueue = getTaskFromGlobalQueue()
                    if (taskFromGlobalQueue != null) {
                        executeTask(taskFromGlobalQueue)
                        continue
                    }
                }

                val taskFromLocalQueue = p.queue.poll()

                if (taskFromLocalQueue != null) {
                    executeTask(taskFromLocalQueue)
                    continue
                }

                val foundTask = findTask()
                if (foundTask != null) {
                    executeTask(foundTask)
                    continue
                }
                break
            }
        }

        private fun getTaskFromGlobalQueue(): Task? {
            globalLock.withLock {
                return globalQueue.poll()
            }
        }

        private fun executeTask(task: Task) {
            val p = processor.value ?: throw IllegalStateException("worker runs without a processor")
            p.scheduleTick.incrementAndGet()

            val taskMode = task.mode
            beforeTask(taskMode)
            runSafely(task)
            afterTask(taskMode)
        }

        private fun beforeTask(taskMode: Int) {
            // todo: handoff if IO
        }

        private fun afterTask(taskMode: Int) {
            // todo: reacquire if IO
        }

        private fun findTask(): Task? {
            val p = processor.value ?: throw IllegalStateException("worker runs without a processor")
            while (true) {
                val taskFromLocalQueue = p.queue.poll()
                if (taskFromLocalQueue != null) {
                    return taskFromLocalQueue
                }

                val taskFromGlobalQueue = getTaskFromGlobalQueue()
                if (taskFromGlobalQueue != null) {
                    return taskFromGlobalQueue
                }

                if (spinning.value || nSpinningWorkers.value * 2 < nProcessors - nIdleProcessors.value) {
                    if (spinning.value) {
                        spinning.value = true
                        nSpinningWorkers.incrementAndGet()
                    }

                    val (task, newWork) = stealTask()
                    if (task != null) {
                        return task
                    }

                    if (newWork) {
                        continue
                    }
                }

                //todo: implement stealing and spinning

                globalLock.withLock {
                    val otherTaskFromGlobalQueue = getTaskFromGlobalQueue()
                    if (otherTaskFromGlobalQueue != null) {
                        return otherTaskFromGlobalQueue
                    }
                    val releasedProcessor = releaseProcessor()
                    if (p != releasedProcessor) {
                        throw IllegalStateException("worker runs without a processor")
                    }
                    returnIdleProcessorToQueue(releasedProcessor)
                }

                val wasSpinning = spinning.value
                if (spinning.value) {
                    spinning.value = false
                    if (nSpinningWorkers.decrementAndGet() < 0) {
                        throw IllegalStateException("negative nSpinningWorkers")
                    }
                    //todo: try find new p with work
                }
                return null
            }
        }

        private fun stealTask(): StolenTask {
            val p = processor.value ?: throw IllegalStateException("worker runs without a processor")

            val stealTries = 4
            repeat(stealTries) { attempt ->
                var pos = nextInt(nProcessors)
                val coprime = randomOrderCoprimes[pos % randomOrderCoprimes.size]
                val stealNextTask = attempt == stealTries - 1
                repeat(nProcessors) {
                    val processor = processors[pos]
                    if (p !== processor) {
                        if (processor.status.value != ProcessorStatus.IDLE) {
                            val stolen = p.queue.tryStealFrom(processor.queue, stealNextTask)
                            if (stolen != null) {
                                return StolenTask(stolen, true)
                            }
                        }
                    }
                    pos += coprime
                    pos %= nProcessors
                }
            }

            return StolenTask(null, false)
        }

//        private fun trySteal(processor: Processor, stealNextTask: Boolean): Task {
//
//        }

        fun nextInt(upperBound: Int): Int {
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

        private fun releaseProcessor(): Processor {
            val p = processor.value ?: throw IllegalStateException("worker runs without a processor")
            if (p.status.value != ProcessorStatus.RUNNING) {
                throw IllegalStateException("worker runs on processor with invalid status ${p.status.value}")
            }
            processor.value = null
            p.worker.value = null
            p.status.value = ProcessorStatus.IDLE
            return p
        }

        private fun returnIdleProcessorToQueue(processor: Processor) {
            if (processor.queue.size != 0) {
                throw IllegalStateException("processor can't be returned to idle queue: it's local queue is not empty")
            }
            processor.nextProcessor.value = idleProcessor.value
            idleProcessor.value = processor
            nIdleProcessors.incrementAndGet()
        }
    }

    internal data class StolenTask(
        val task: Task?,
        val newWork: Boolean,
    )

    fun runSafely(task: Task) {
        try {
            task.run()
        } catch (e: Throwable) {
            val thread = Thread.currentThread()
            thread.uncaughtExceptionHandler.uncaughtException(thread, e)
        }
    }

    override fun execute(command: Runnable) = dispatch(command)

    override fun close() {

    }

    fun shutdown(timeout: Long) {

    }
}
