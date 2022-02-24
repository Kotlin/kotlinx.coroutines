/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import java.util.concurrent.*
import kotlin.math.*

public interface BoundedBlockingQueue<E : Any> {
    public fun send(element: E)
    public fun sendSingleProducer(element: E)
    public fun receive(): E
    public fun receiveSingleConsumer(): E
}

public class ArrayBlockingQueueJava<E: Any>(capacity: Int, fair: Boolean) : ArrayBlockingQueue<E>(capacity, fair), BoundedBlockingQueue<E> {
    override fun send(element: E): Unit = put(element)
    override fun sendSingleProducer(element: E): Unit = send(element)
    override fun receive(): E = take()
    override fun receiveSingleConsumer(): E = receive()
}

public class LinkedBlockingQueueJava<E: Any>(capacity: Int) : LinkedBlockingQueue<E>(capacity), BoundedBlockingQueue<E> {
    override fun send(element: E): Unit = put(element)
    override fun sendSingleProducer(element: E): Unit = send(element)
    override fun receive(): E = take()
    override fun receiveSingleConsumer(): E = receive()
}

public abstract class BoundedBlockingQueueSimpleBase<E: Any>(capacity: Int, fair: Boolean) : BoundedBlockingQueue<E> {
//    private val semaphoreToRetrieve = Semaphore(Int.MAX_VALUE / 2).also { it.acquire(Int.MAX_VALUE / 2) }
    private val semaphoreToRetrieve = SemaSQS_Async_Simple(permits = Int.MAX_VALUE / 2, acquiredPermits = Int.MAX_VALUE / 2, fair = fair)
//    private val semaphoreToSend = Semaphore(Int.MAX_VALUE / 2).also { it.acquire(Int.MAX_VALUE / 2 - capacity) }
    private val semaphoreToSend = SemaSQS_Async_Simple(permits = Int.MAX_VALUE / 2, acquiredPermits = Int.MAX_VALUE / 2 - capacity, fair = fair)

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
public class BoundedBlockingQueueSimpleQueue<E: Any>(capacity: Int, fair: Boolean) : BoundedBlockingQueueSimpleBase<E>(capacity, fair) {
    private val q = FastConcurrentQueue<E>()

    override fun enqueue(element: E): Unit = q.enqueue(element)
    override fun enqueueSingleProducer(element: E): Unit = q.enqueueSingleProducer(element)
    override fun dequeue(): E = q.dequeue()!!
    override fun dequeueSingleConsumer(): E = q.dequeueSingleConsumer()!!
}
public class BoundedBlockingQueueSimpleArray<E: Any>(capacity: Int, fair: Boolean) : BoundedBlockingQueueSimpleBase<E>(capacity, fair) {
    private val shift = ceil(log2(capacity.toDouble())).toInt()
    private val mask = (1L shl shift) - 1
    private val a = atomicArrayOfNulls<E>(1 shl shift)
    private val enqIdx = atomic(0L)
    private val deqIdx = atomic(0L)

    override fun enqueue(element: E) {
        val i = (enqIdx.getAndIncrement() and mask).toInt()
        while (true) {
            if (a[i].value != null) continue
            if (a[i].compareAndSet(null, element)) break
        }
    }
    override fun enqueueSingleProducer(element: E) {
        val curEnqIdx = enqIdx.value
        enqIdx.lazySet(curEnqIdx + 1)
        val i = (curEnqIdx and mask).toInt()
        while (a[i].value != null) {}
        a[i].value = element
    }
    override fun dequeue(): E  {
        val i = (deqIdx.getAndIncrement() and mask).toInt()
        var element: E?
        while (true) {
            element = a[i].value
            if (element == null) continue
            if (a[i].compareAndSet(element, null)) break
        }
        return element!!
    }

    override fun dequeueSingleConsumer(): E {
        val curDeqIdx = deqIdx.value
        deqIdx.lazySet(curDeqIdx + 1)
        val i = (curDeqIdx and mask).toInt()
        var element: E? = null
        while (element == null) {
            element = a[i].value
        }
        a[i].value = null
        return element
    }
}

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE", "INVISIBLE_OVERRIDE", "CANNOT_OVERRIDE_INVISIBLE_MEMBER")
public abstract class BoundedBlockingQueueSmartBase<E : Any, S>(capacity: Int, private val fair: Boolean) : BoundedBlockingQueue<E> {
    private val deqIdxAndSendPermits = atomic((capacity + INITIAL) * PERMIT)
    private val enqIdxAndReceivePermits = atomic(INITIAL * PERMIT)

    private val _releasedSendPermits = atomic(0)
    private val _releasedReceivePermits = atomic(0)


    private val cqsToRetrieve = object : SegmentQueueSynchronizerJVM<Unit>() {
        override val resumeMode get() = ResumeMode.ASYNC
    }
    private val cqsToSend = object : SegmentQueueSynchronizerJVM<Unit>() {
        override val resumeMode get() = ResumeMode.ASYNC
    }

    internal abstract fun retrieveElement(index: Long, s: S): E
    internal abstract fun storeElement(index: Long, element: E, s: S)

    override fun send(element: E) {
        val sendPermits = decSendPermits()
        if (sendPermits <= 0) {
            while (true) {
                if (!fair && _releasedSendPermits.value > 0) {
                    val rp = _releasedSendPermits.getAndDecrement()
                    if (rp > 0) break
                    if (_releasedSendPermits.getAndIncrement() >= 0) continue
                }
                cqsToSend.suspendCurThread()
                if (fair) break
            }
        }
        incEnqIndexAndReceivePermits(this::sendBeforeEnqIdxInc) { index, receivePermits, s ->
            storeElement(index, element, s)
            if (receivePermits < 0) {
                if (!fair) {
                    _releasedReceivePermits.getAndIncrement()
                }
                cqsToRetrieve.resume(Unit)
            }
        }
    }

    override fun receive(): E {
        val receivePermits = decReceivePermits()
        if (receivePermits <= 0) {
            while (true) {
                if (!fair && _releasedReceivePermits.value > 0) {
                    val rp = _releasedReceivePermits.getAndDecrement()
                    if (rp > 0) break
                    if (_releasedReceivePermits.getAndIncrement() >= 0) continue
                }
                cqsToRetrieve.suspendCurThread()
                if (fair) break
            }
        }
        incDeqIndexAndSendPermits(this::receiveBeforeDeqIdxInc) { index, sendPermits, s ->
            val element = retrieveElement(index, s)
            if (sendPermits < 0) {
                if (!fair) {
                    _releasedSendPermits.getAndIncrement()
                }
                cqsToSend.resume(Unit)
            }
            return element
        }
    }

    protected abstract fun sendBeforeEnqIdxInc(): S
    protected abstract fun receiveBeforeDeqIdxInc(): S

    override fun sendSingleProducer(element: E): Unit = send(element)
    override fun receiveSingleConsumer(): E = receive()

    internal inline fun <S, R> incEnqIndexAndReceivePermits(setupBlock: () -> S, block: (index: Long, permits: Int, S) -> R): R {
        val s = setupBlock()
        val curEnqIdxAndReceivePermits = enqIdxAndReceivePermits.getAndAdd(INDEX + PERMIT)
        val index = curEnqIdxAndReceivePermits.index
        val permits = curEnqIdxAndReceivePermits.permits
        return block(index, permits, s)
    }
    internal inline fun <S, R> incDeqIndexAndSendPermits(setupBlock: () -> S, block: (index: Long, permits: Int, S) -> R): R {
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

internal class BoundedBlockingQueueSmartArray<E : Any>(capacity: Int, fair: Boolean) : BoundedBlockingQueueSmartBase<E, Unit>(capacity, fair) {
    private val a = atomicArrayOfNulls<E>(capacity * 4)

    override fun retrieveElement(index: Long, ignored: Unit): E {
        val i = (index % a.size).toInt()
        var element: E?
        while (true) {
            element = a[i].value
            if (element == null) continue
            if (a[i].compareAndSet(element, null)) break
        }
        return element!!
    }

    override fun storeElement(index: Long, element: E, ignored: Unit) {
        val i = (index % a.size).toInt()
        while (true) {
            if (a[i].value != null) continue
            if (a[i].compareAndSet(null, element)) break
        }
    }

    override fun sendBeforeEnqIdxInc() = Unit
    override fun receiveBeforeDeqIdxInc() = Unit
}

internal class SemaSQS_Async_Simple(permits: Int, acquiredPermits: Int = 0, val fair: Boolean): SegmentQueueSynchronizerJVM<Unit>() {
    override val resumeMode get() = ResumeMode.ASYNC
    override val cancellationMode: CancellationMode get() = CancellationMode.SIMPLE

    private val _availablePermits = atomic(permits - acquiredPermits)
    private val _releasedPermits = atomic(0)

    fun acquire() {
        val p = _availablePermits.getAndDecrement()
        if (p > 0) return
        while (true) {
            if (!fair && _releasedPermits.value > 0) {
                val rp = _releasedPermits.getAndDecrement()
                if (rp > 0) return
                if (_releasedPermits.getAndIncrement() >= 0) continue
            }
            suspendCurThread()
            if (fair) return
        }
    }

    fun release() {
        while (true) {
            val p = _availablePermits.getAndIncrement()
            if (p >= 0) return
            if (!fair) {
                _releasedPermits.getAndIncrement()
            }
            if (resume(Unit)) return
        }
    }
}

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE", "INVISIBLE_OVERRIDE", "CANNOT_OVERRIDE_INVISIBLE_MEMBER")
internal class BoundedBlockingQueueSmartQueue<E : Any>(capacity: Int, fair: Boolean) : BoundedBlockingQueueSmartBase<E, FastConcurrentQueueSegment>(capacity, fair) {
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

    override fun sendBeforeEnqIdxInc(): FastConcurrentQueueSegment = enqSegm.value
    override fun receiveBeforeDeqIdxInc(): FastConcurrentQueueSegment = deqSegm.value

    private fun FastConcurrentQueueSegment.findSegment(id: Long): FastConcurrentQueueSegment =
        findSegmentInternal(id, ::createFastConcurrentQueueSegment).segment

    private fun findSegmentAndMoveForwardEnqueue(id: Long, start: FastConcurrentQueueSegment): FastConcurrentQueueSegment =
        enqSegm.findSegmentAndMoveForward(id, start, ::createFastConcurrentQueueSegment).segment

    private fun findSegmentAndMoveForwardDequeue(id: Long, start: FastConcurrentQueueSegment): FastConcurrentQueueSegment =
        deqSegm.findSegmentAndMoveForward(id, start, ::createFastConcurrentQueueSegment).segment
}

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE", "INVISIBLE_OVERRIDE", "CANNOT_OVERRIDE_INVISIBLE_MEMBER")
public class FastConcurrentQueue<E : Any> {
    private val _deqIdx = atomic(0L)
    private val _enqIdx = atomic(0L)

    private val deqSegm: AtomicRef<FastConcurrentQueueSegment>
    private val enqSegm: AtomicRef<FastConcurrentQueueSegment>

    init {
        val s = FastConcurrentQueueSegment(id = 0)
        deqSegm = atomic(s)
        enqSegm = atomic(s)
    }

    public fun enqueueSingleProducer(x: E) {
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

    public fun enqueue(x: E) {
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


    public fun dequeue(): E? {
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

    public fun dequeueSingleConsumer(): E? {
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