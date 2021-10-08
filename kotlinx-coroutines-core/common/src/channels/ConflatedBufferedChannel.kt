/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.locks.*
import kotlinx.coroutines.channels.BufferOverflow.*
import kotlinx.coroutines.channels.ChannelResult.Companion.success
import kotlinx.coroutines.internal.OnUndeliveredElement
import kotlin.math.*

/**
 * Channel with array buffer of a fixed capacity.
 * Sender suspends only when buffer is full and receiver suspends only when buffer is empty.
 *
 * This channel is created by `Channel(capacity)` factory function invocation.
 *
 * This implementation uses lock to protect the buffer, which is held only during very short buffer-update operations.
 * The lists of suspended senders or receivers are lock-free.
 **/
internal open class ConflatedBufferedChannel<E>(
    /**
     * Buffer capacity.
     */
    private val capacity: Int,
    private val onBufferOverflow: BufferOverflow,
    onUndeliveredElement: OnUndeliveredElement<E>?
) : BufferedChannel<E>(capacity = Channel.RENDEZVOUS, onUndeliveredElement = onUndeliveredElement) {
    private val lock = reentrantLock()

    /*
     * Guarded by lock.
     * Allocate minimum of capacity and 8 to avoid excess memory pressure for large channels when it's not necessary.
     */
    private var buffer: Array<Any?> = arrayOfNulls<Any?>(min(capacity, 8))

    private var head: Int = 0
    private var size: Int = 0 // Invariant: size <= capacity


    init {
        require(onBufferOverflow !== SUSPEND) {
            "This implementation does not support suspension for senders, use ${BufferedChannel::class.simpleName} instead"
        }
        require(capacity >= 1) {
           "Buffered channel capacity must be at least 1, but $capacity was specified"
        }
    }

    override fun tryReceive(): ChannelResult<E> = lock.withLock { tryReceiveImpl() }

    private fun tryReceiveImpl(): ChannelResult<E> =
        if (size != 0) success(retrieve())
        else super.tryReceive()

    override suspend fun receive(): E {
        lock.lock()
        tryReceiveImpl()
            .onSuccess { element ->
                lock.unlock()
                return element
            }.onClosed { cause ->
                lock.unlock()
                throw cause ?: ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE)
            }
        return super.receive()
    }

    override suspend fun receiveCatching(): ChannelResult<E> {
        lock.lock()
        val result = tryReceiveImpl()
        if (result.isSuccess || result.isClosed) {
            lock.unlock()
            return result
        }
        return super.receiveCatching()
    }

    override fun onReceiveEnqueued() {
        lock.unlock()
    }

    override fun trySend(element: E): ChannelResult<Unit> = lock.withLock {
        val attempt = super.trySend(element)
        if (attempt.isSuccess || attempt.isClosed) return attempt
        ensureBufferSize(size + 1)
        insert(element)
        return success(Unit)
    }

    private fun ensureBufferSize(newSize: Int) {
        if (buffer.size < newSize) {
            replaceBuffer(min(capacity, buffer.size * 2))
        } else if (newSize < buffer.size / 4) {
            replaceBuffer(buffer.size / 2)
        }
    }

    private fun replaceBuffer(newBufferCapacity: Int) {
        val newBuffer = arrayOfNulls<Any?>(newBufferCapacity)
        val curSize = size
        repeat(curSize) { i ->
            newBuffer[i] = retrieve()
        }
        buffer = newBuffer
        head = 0
        size = curSize
    }

    private fun retrieve(): E {
        val i = head++
        head %= buffer.size
        val element = buffer[i] as E
        buffer[i] = null
        size--
        return element
    }

    private fun insert(element: E) {
        if (size == capacity) { // overflow
            if (onBufferOverflow === DROP_LATEST) return // do nothing
            if (onBufferOverflow === DROP_OLDEST) {
                retrieve() // drop the first element
                insert(element)
            }
        } else {
            val i = (head + size) % buffer.size
            size++
            buffer[i] = element
        }
    }

    override suspend fun send(element: E) {
        offer(element)
    }

    override val isEmpty: Boolean
        get() = lock.withLock { size == 0 && super.isEmpty }

    override fun closeImpl(cause: Throwable?, cancel: Boolean): Boolean = lock.withLock {
        super.closeImpl(cause, cancel)
    }

    override fun cancelImpl(cause: Throwable?): Boolean = lock.withLock {
        buffer = emptyArray()
        head = 0
        size = 0
        super.cancelImpl(cause)
    }

    override val isClosedForReceive: Boolean get() = lock.withLock {
        if (size > 0) false
        else super.isClosedForReceive
    }
}
