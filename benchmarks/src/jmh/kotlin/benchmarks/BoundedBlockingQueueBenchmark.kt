/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package benchmarks

import benchmarks.common.*
import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import org.openjdk.jmh.annotations.*
import java.util.concurrent.*
import kotlin.concurrent.*

@Warmup(iterations = 3, time = 500, timeUnit = TimeUnit.MICROSECONDS)
@Measurement(iterations = 10, time = 500, timeUnit = TimeUnit.MICROSECONDS)
@Fork(value = 3)
@BenchmarkMode(Mode.AverageTime)
@OutputTimeUnit(TimeUnit.MILLISECONDS)
@State(Scope.Benchmark)
open class BoundedBlockingQueueBenchmark {
    @Param("1", "4", "16", "64")
    var capacity: Int = 0

    @Param("1", "2", "4")
    var threads: Int = 0

    @Param
    var algo: BCQAlgo = BCQAlgo.values()[0]

    @Param("100", "300", "1000")
    var work: Int = 0

    lateinit var q: BoundedBlockingQueue<String>

    @Setup
    fun setup() {
        q = algo.create(capacity)
    }

    @Benchmark
    fun spmc() {
        val producers = 1
        val consumers = Integer.max(1, threads - 1)
        run(producers, consumers)
    }

    @Benchmark
    fun mpsc() {
        val consumers = 1
        val producers = Integer.max(1, threads - 1)
        run(producers, consumers)
    }

    @Benchmark
    fun mpmc() {
        val producers = (threads + 1) / 2
        val consumers = producers
        run(producers, consumers)
    }

    private fun run(producers: Int, consumers: Int) {
        val n = APPROX_BATCH_SIZE / producers * producers
        val phaser = Phaser(producers + consumers + 1)
        // Run producers
        repeat(producers) {
            thread {
                repeat(n / producers) {
                    q.send(VALUES[it])
                    doGeomDistrWork(work)
                }
                phaser.arrive()
            }
        }
        // Run consumers
        repeat(consumers) {
            thread {
                repeat(n / consumers) {
                    q.receive()
                    doGeomDistrWork(work)
                }
                phaser.arrive()
            }
        }
        // Wait until work is done
        phaser.arriveAndAwaitAdvance()
    }
}

private const val APPROX_BATCH_SIZE = 100_000
private val VALUES = (0 until APPROX_BATCH_SIZE).map { "$it" }


enum class BCQAlgo(val create: (capacity: Int) -> BoundedBlockingQueue<String>) {
    JAVA_ARRAY({ArrayBlockingQueueJava(it)}),
    JAVA_LINKED({LinkedBlockingQueueJava(it)}),
    SIMPLE_ARRAY({BoundedBlockingQueueSimpleArray(it)}),
    SIMPLE_QUEUE({BoundedBlockingQueueSimpleQueue(it)}),
    SMART_QUEUE({BoundedBlockingQueueSmartQueue(it)}),
}

interface BoundedBlockingQueue<E : Any> {
    fun send(element: E)
    fun sendSingleProducer(element: E)
    fun receive(): E
    fun receiveSingleConsumer(): E
}

class ArrayBlockingQueueJava<E: Any>(capacity: Int) : ArrayBlockingQueue<E>(capacity, true), BoundedBlockingQueue<E> {
    override fun send(element: E) = put(element())
    override fun sendSingleProducer(element: E) = send(element)
    override fun receive(): E = take()
    override fun receiveSingleConsumer(): E = receive()
}

class LinkedBlockingQueueJava<E: Any>(capacity: Int) : LinkedBlockingQueue<E>(capacity), BoundedBlockingQueue<E> {
    override fun send(element: E) = put(element())
    override fun sendSingleProducer(element: E) = send(element)
    override fun receive(): E = take()
    override fun receiveSingleConsumer(): E = receive()
}

abstract class BoundedBlockingQueueSimpleBase<E: Any>(capacity: Int) : BoundedBlockingQueue<E> {
    private val semaphoreToRetrieve = SemaSQS_Async_Simple(permits = Int.MAX_VALUE / 2, acquiredPermits = Int.MAX_VALUE / 2)
    private val semaphoreToSend = SemaSQS_Async_Simple(permits = Int.MAX_VALUE / 2, acquiredPermits = Int.MAX_VALUE / 2 - capacity)

    override fun send(element: E) {
        semaphoreToSend.acquire()
        enqueue(element)
        semaphoreToRetrieve.release()
    }
    override fun sendSingleProducer(element: E) {
        semaphoreToSend.acquire()
        enqueueSingleProducer(element)
        semaphoreToRetrieve.release()
    }

    override fun receive(): E {
        semaphoreToRetrieve.acquire()
        val element = dequeue()
        semaphoreToSend.release()
        return element
    }
    override fun receiveSingleConsumer(): E {
        semaphoreToRetrieve.acquire()
        val element = dequeueSingleConsumer()
        semaphoreToSend.release()
        return element
    }

    protected abstract fun enqueue(element: E)
    protected abstract fun enqueueSingleProducer(element: E)
    protected abstract fun dequeue(): E
    protected abstract fun dequeueSingleConsumer(): E
}
private class BoundedBlockingQueueSimpleQueue<E: Any>(capacity: Int) : BoundedBlockingQueueSimpleBase<E>(capacity) {
    private val q = FastConcurrentQueue<E>()

    override fun enqueue(element: E) = q.enqueue(element)
    override fun enqueueSingleProducer(element: E) = q.enqueueSingleProducer(element)
    override fun dequeue(): E = q.dequeue()!!
    override fun dequeueSingleConsumer(): E = q.dequeueSingleConsumer()!!
}
private class BoundedBlockingQueueSimpleArray<E: Any>(capacity: Int) : BoundedBlockingQueueSimpleBase<E>(capacity) {
    private val a = atomicArrayOfNulls<E>(capacity)
    private val enqIdx = atomic(0L)
    private val deqIdx = atomic(0L)

    override fun enqueue(element: E) {
        val i = (enqIdx.getAndIncrement() % a.size).toInt()
        while (a[i].value != null) {}
        a[i].value = element
    }
    override fun enqueueSingleProducer(element: E) {
        val curEnqIdx = enqIdx.value
        enqIdx.lazySet(curEnqIdx + 1)
        val i = (curEnqIdx % a.size).toInt()
        while (a[i].value != null) {}
        a[i].value = element
    }
    override fun dequeue(): E  {
        val i = (deqIdx.getAndIncrement() % a.size).toInt()
        var element: E? = null
        while (element == null) {
            element = a[i].value
        }
        a[i].value = null
        return element
    }

    override fun dequeueSingleConsumer(): E {
        val curDeqIdx = deqIdx.value
        deqIdx.lazySet(curDeqIdx + 1)
        val i = (curDeqIdx % a.size).toInt()
        var element: E? = null
        while (element == null) {
            element = a[i].value
        }
        a[i].value = null
        return element
    }
}

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE", "INVISIBLE_OVERRIDE", "CANNOT_OVERRIDE_INVISIBLE_MEMBER")
private abstract class BoundedBlockingQueueSmartBase<E : Any, S>(capacity: Int) : BoundedBlockingQueue<E> {
    private val deqIdxAndSendPermits = atomic((capacity + INITIAL) * PERMIT)
    private val enqIdxAndReceivePermits = atomic(INITIAL * PERMIT)

    private val cqsToRetrieve = object : SegmentQueueSynchronizerJVM<Unit>() {
        override val resumeMode get() = ResumeMode.ASYNC
    }
    private val cqsToSend = object : SegmentQueueSynchronizerJVM<Unit>() {
        override val resumeMode get() = ResumeMode.ASYNC
    }

    protected abstract fun retrieveElement(index: Long, s: S): E
    protected abstract fun storeElement(index: Long, element: E, s: S)

    override fun send(element: E) {
        val sendPermits = decSendPermits()
        if (sendPermits <= 0) {
            cqsToSend.suspendCurThread()
        }
        incEnqIndexAndReceivePermits(this::sendBeforeEnqIdxInc) { index, receivePermits, s ->
            storeElement(index, element, s)
            if (receivePermits < 0) {
                cqsToRetrieve.resume(Unit)
            }
        }
    }

    override fun receive(): E {
        val receivePermits = decReceivePermits()
        if (receivePermits <= 0) {
            cqsToRetrieve.suspendCurThread()
        }
        incDeqIndexAndSendPermits(this::receiveBeforeDeqIdxInc) { index, sendPermits, s ->
            val element = retrieveElement(index, s)
            if (sendPermits < 0) {
                cqsToSend.resume(Unit)
            }
            return element
        }
    }

    protected abstract fun sendBeforeEnqIdxInc(): S
    protected abstract fun receiveBeforeDeqIdxInc(): S

    override fun sendSingleProducer(element: E) = send(element)
    override fun receiveSingleConsumer() = receive()

    protected inline fun <S, R> incEnqIndexAndReceivePermits(setupBlock: () -> S, block: (index: Long, permits: Int, S) -> R): R {
        val s = setupBlock()
        val curEnqIdxAndReceivePermits = enqIdxAndReceivePermits.getAndAdd(INDEX + PERMIT)
        val index = curEnqIdxAndReceivePermits.index
        val permits = curEnqIdxAndReceivePermits.permits
        return block(index, permits, s)
    }
    protected inline fun <S, R> incDeqIndexAndSendPermits(setupBlock: () -> S, block: (index: Long, permits: Int, S) -> R): R {
        val s = setupBlock()
        val curDeqIdxAndSendPermits = deqIdxAndSendPermits.getAndAdd(INDEX + PERMIT)
        val index = curDeqIdxAndSendPermits.index
        val permits = curDeqIdxAndSendPermits.permits
        return block(index, permits, s)
    }

    protected fun incEnqIndex(): Long =
        enqIdxAndReceivePermits.getAndAdd(INDEX).index
    protected fun incDeqIndex(): Long =
        deqIdxAndSendPermits.getAndAdd(INDEX).index

    protected fun decReceivePermits(): Int =
        enqIdxAndReceivePermits.getAndAdd(-PERMIT).permits
    protected fun decSendPermits(): Int =
        deqIdxAndSendPermits.getAndAdd(-PERMIT).permits
}
private const val INITIAL = 1 shl 8
private const val OFFSET = 10
private const val MASK = (1L shl OFFSET) - 1
private const val PERMIT = 1L
private const val INDEX = 1L shl OFFSET
private inline val Long.permits: Int get() = (this and MASK).toInt() - INITIAL
private inline val Long.index: Long get() = this shr OFFSET

private class BoundedBlockingQueueSmartArray<E : Any>(capacity: Int) : BoundedBlockingQueueSmartBase<E, Unit>(capacity) {
    private val a = atomicArrayOfNulls<E>(capacity * 2)

    override fun retrieveElement(index: Long, ignored: Unit): E {
        val i = (index % a.size).toInt()
        var element: E? = null
        while (element == null) {
            element = a[i].value
        }
        a[i].value = null
        return element
    }

    override fun storeElement(index: Long, element: E, ignored: Unit) {
        val i = (index % a.size).toInt()
        while (a[i].value != null) {}
        a[i].value = element
    }

    override fun sendBeforeEnqIdxInc() = Unit
    override fun receiveBeforeDeqIdxInc() = Unit
}

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE", "INVISIBLE_OVERRIDE", "CANNOT_OVERRIDE_INVISIBLE_MEMBER")
private class BoundedBlockingQueueSmartQueue<E : Any>(capacity: Int) : BoundedBlockingQueueSmartBase<E, FastConcurrentQueueSegment>(capacity) {
    private val deqSegm: AtomicRef<FastConcurrentQueueSegment>
    private val enqSegm: AtomicRef<FastConcurrentQueueSegment>

    init {
        val s = FastConcurrentQueueSegment(id = 0)
        deqSegm = atomic(s)
        enqSegm = atomic(s)
    }

    override fun storeElement(index: Long, element: E, segm: FastConcurrentQueueSegment) {
        var segm = segm
        val id = index / SIZE
        val i = (index % SIZE).toInt()
        if (segm.id != id) {
            segm = findSegmentAndMoveForwardEnqueue(id, segm)
        }
        segm.install(i, element)
    }

    override fun retrieveElement(index: Long, segm: FastConcurrentQueueSegment): E {
        var segm = segm
        val id = index / SIZE
        val i = (index % SIZE).toInt()
        if (segm.id != id) {
            segm = findSegmentAndMoveForwardDequeue(id, segm)
        }
        return segm.extractBlocking(i) as E
    }

    override fun sendBeforeEnqIdxInc() = enqSegm.value
    override fun receiveBeforeDeqIdxInc() = deqSegm.value

    private fun FastConcurrentQueueSegment.findSegment(id: Long): FastConcurrentQueueSegment =
        findSegmentInternal(id, ::createFastConcurrentQueueSegment).segment

    private fun findSegmentAndMoveForwardEnqueue(id: Long, start: FastConcurrentQueueSegment): FastConcurrentQueueSegment =
        enqSegm.findSegmentAndMoveForward(id, start, ::createFastConcurrentQueueSegment).segment

    private fun findSegmentAndMoveForwardDequeue(id: Long, start: FastConcurrentQueueSegment): FastConcurrentQueueSegment =
        deqSegm.findSegmentAndMoveForward(id, start, ::createFastConcurrentQueueSegment).segment
}

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE", "INVISIBLE_OVERRIDE", "CANNOT_OVERRIDE_INVISIBLE_MEMBER")
class FastConcurrentQueue<E : Any> {
    private val _deqIdx = atomic(0L)
    private val _enqIdx = atomic(0L)

    private val deqSegm: AtomicRef<FastConcurrentQueueSegment>
    private val enqSegm: AtomicRef<FastConcurrentQueueSegment>

    init {
        val s = FastConcurrentQueueSegment(id = 0)
        deqSegm = atomic(s)
        enqSegm = atomic(s)
    }

    fun enqueueSingleProducer(x: E) {
        while (true) {
            var s = enqSegm.value
            val enqIdx = _enqIdx.value
            _enqIdx.lazySet(enqIdx + 1)
            val id = enqIdx / SIZE
            val i = (enqIdx % SIZE).toInt()
            if (s.id != id) {
                s = s.findSegment(id)
                enqSegm.lazySet(s)
            }
            if (s.tryInstall(i, x)) return
        }
    }

    private fun FastConcurrentQueueSegment.findSegment(id: Long): FastConcurrentQueueSegment =
        findSegmentInternal(id, ::createFastConcurrentQueueSegment).segment

    fun enqueue(x: E) {
        while (true) {
            var s = enqSegm.value
            val enqIdx = _enqIdx.getAndIncrement()
            val id = enqIdx / SIZE
            val i = (enqIdx % SIZE).toInt()
            if (s.id != id) {
                s = findSegmentAndMoveForwardEnqueue(id, s)
            }
            if (s.tryInstall(i, x)) return
        }
    }

    private fun findSegmentAndMoveForwardEnqueue(id: Long, start: FastConcurrentQueueSegment): FastConcurrentQueueSegment =
        enqSegm.findSegmentAndMoveForward(id, start, ::createFastConcurrentQueueSegment).segment

    private fun findSegmentAndMoveForwardDequeue(id: Long, start: FastConcurrentQueueSegment): FastConcurrentQueueSegment =
        deqSegm.findSegmentAndMoveForward(id, start, ::createFastConcurrentQueueSegment).segment


    fun dequeue(): E? {
        while (true) {
//            if (_deqIdx.value >= _enqIdx.value) return null // TODO remove this line
            var s = deqSegm.value
            val deqIdx = _deqIdx.getAndIncrement()
            val id = deqIdx / SIZE
            val i = (deqIdx % SIZE).toInt()
            if (s.id != id) {
                s = findSegmentAndMoveForwardDequeue(id, s)
            }
            val e = s.tryExtract(i)
            if (e != null) return e as E
        }
    }

    fun dequeueSingleConsumer(): E? {
        while (true) {
//            if (_deqIdx.value >= _enqIdx.value) return null // TODO remove this line
            var s = deqSegm.value
            val deqIdx = _deqIdx.value
            _deqIdx.lazySet(deqIdx + 1)
            val id = deqIdx / SIZE
            val i = (deqIdx % SIZE).toInt()
            if (s.id != id) {
                s = s.findSegment(id)
                deqSegm.lazySet(s)
            }
            val e = s.tryExtract(i)
            if (e != null) return e as E
        }
    }
}
@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE", "INVISIBLE_OVERRIDE", "CANNOT_OVERRIDE_INVISIBLE_MEMBER")
internal class FastConcurrentQueueSegment(id: Long) : Segment<FastConcurrentQueueSegment>(id, null, 0) {
    private val a = atomicArrayOfNulls<Any?>(SIZE)

    override val maxSlots: Int get() = SIZE
    override val supportRemoves get() = false

    fun tryInstall(i: Int, value: Any) = a[i].compareAndSet(null, value)

    fun install(i: Int, value: Any) {
        a[i].value = value
    }

    fun tryExtract(i: Int): Any? {
        val e = a[i].value
        if (e != null) {
            a[i].lazySet(null)
            return e
        }
        return a[i].getAndSet(BROKEN)
    }

    fun extractBlocking(i: Int): Any {
        var e: Any? = null
        while (e === null) {
            e = a[i].value
        }
        a[i].lazySet(null)
        return e
    }
}
private fun createFastConcurrentQueueSegment(id: Long, prev: FastConcurrentQueueSegment?) = FastConcurrentQueueSegment(id)
private val BROKEN = Any()
private const val SIZE = 64