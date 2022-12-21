/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.locks.*
import kotlinx.coroutines.assert
import kotlinx.coroutines.channels.BufferOverflow.*
import kotlinx.coroutines.channels.ChannelResult.Companion.success
import kotlinx.coroutines.internal.callUndeliveredElement
import kotlinx.coroutines.internal.OnUndeliveredElement
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*

/**
 * Channel with array buffer of a fixed capacity.
 * Sender suspends only when buffer is full and receiver suspends only when buffer is empty.
 *
 * This channel is created by `Channel(capacity)` factory function invocation.
 *
 * This implementation is blocking and uses coarse-grained locking to protect all channel operations.
 * However, removing a cancelled sender or receiver from a list of waiters is lock-free.
 **/
internal open class ConflatedBufferedChannel<E>(
    private val capacity: Int,
    private val onBufferOverflow: BufferOverflow,
    onUndeliveredElement: OnUndeliveredElement<E>? = null
) : BufferedChannel<E>(capacity = capacity, onUndeliveredElement = onUndeliveredElement) {
    private val lock = reentrantLock() // guards all channel operations

    init {
        require(onBufferOverflow !== SUSPEND) {
            "This implementation does not support suspension for senders, use ${BufferedChannel::class.simpleName} instead"
        }
        require(capacity >= 1) {
            "Buffered channel capacity must be at least 1, but $capacity was specified"
        }
    }

    override suspend fun receive(): E {
        // Acquire the lock in the beginning of receive operation.
        // Once the synchronization is completed (either the first
        // element is retrieved, the operation suspends, or this
        // channel is discovered in the closed state without element),
        // `onReceiveSynchronizationCompletion` must be called by the
        // underneath buffered channel implementation.
        lock.lock()
        return super.receive()
    }

    override suspend fun receiveCatching(): ChannelResult<E> {
        // Acquire the lock in the beginning of receive operation.
        // It automatically releases once the synchronization completes.
        // See `receive` operation for details.
        lock.lock()
        return super.receiveCatching()
    }

    override fun tryReceive(): ChannelResult<E> {
        // Acquire the lock in the beginning of receive operation.
        // It automatically releases once the synchronization completes.
        // See `receive` operation for details.
        lock.lock()
        return super.tryReceive()
    }

    override fun registerSelectForReceive(select: SelectInstance<*>, ignoredParam: Any?) {
        // Acquire the lock in the beginning of receive operation.
        // It automatically releases once the synchronization completes.
        // See `receive` operation for details.
        lock.lock()
        super.registerSelectForReceive(select, ignoredParam)
    }

    override fun iterator(): ChannelIterator<E> = ConflatedChannelIterator()

    private inner class ConflatedChannelIterator : BufferedChannelIterator() {
        override suspend fun hasNext(): Boolean {
            // Acquire the lock in the beginning of receive operation.
            // It automatically releases once the synchronization completes.
            // See `receive` operation for details.
            lock.lock()
            return super.hasNext()
        }
    }

    override fun onReceiveSynchronizationCompleted() {
        // Release the lock once the receive synchronization is done.
        lock.unlock()
    }

    override suspend fun send(element: E) {
        // Should never suspend, implement via `trySend(..)`.
        val attempt = trySend(element)
        if (attempt.isClosed) {
            onUndeliveredElement?.callUndeliveredElement(element, coroutineContext)
            throw sendException
        }
        assert { attempt.isSuccess }
    }

    override fun trySend(element: E): ChannelResult<Unit> = lock.withLock { // guard the operation by lock
        // Is the buffer already full and the channel is not closed?
        // In other words, should the plain `send(..)` operation on
        // the buffer channel under the hood suspend?
        if (!super.shouldSendSuspend()) {
            // There is either a waiting receiver, space in the buffer,
            // or this channel is closed for sending.
            // Try to send the element into the buffered channel underhood.
            return super.trySend(element).also {
                assert { it.isClosed || it.isSuccess }
            }
        }
        // The plain `send(..)` operation is bound to suspend.
        // Either drop the latest or the older element, invoking
        // `onUndeliveredElement` on it.
        if (onBufferOverflow === DROP_LATEST) {
            onUndeliveredElement?.invoke(element)
        } else { // DROP_OLDEST
            // Receive the oldest element. The call below
            // does not invoke `onReceiveSynchronizationCompletion`.
            val oldestElement = tryReceiveInternal().getOrThrow()
            // Now, it is possible to send the element -- do it!
            super.trySend(element).also {
                assert { it.isSuccess }
            }
            // Finally, invoke `onUndeliveredElement`
            // handler on the dropped oldest element.
            onUndeliveredElement?.invoke(oldestElement)
        }
        return success(Unit)
    }

    override suspend fun sendBroadcast(element: E): Boolean {
        trySend(element) // fails only when this channel is closed.
            .onSuccess { return true }
            .onClosed { return false }
        error("unreachable")
    }

    @Suppress("UNCHECKED_CAST")
    override fun registerSelectForSend(select: SelectInstance<*>, element: Any?) {
        // The plain `send(..)` operation never suspends. Thus, either this
        // attempt to send the element succeeds or the channel is closed.
        // In any case, complete this `select` in the registration phase.
        trySend(element as E).let {
            it.onSuccess {
                select.selectInRegistrationPhase(Unit)
                return
            }.onClosed {
                select.selectInRegistrationPhase(CHANNEL_CLOSED)
                return
            }
        }
        error("unreachable")
    }

    override fun shouldSendSuspend() = false // never suspends

    override fun close(cause: Throwable?) = lock.withLock { // protected by lock
        super.close(cause)
    }

    override fun cancelImpl(cause: Throwable?) = lock.withLock { // protected by lock
        super.cancelImpl(cause)
    }

    override val isClosedForSend: Boolean
        get() = lock.withLock { super.isClosedForSend } // protected by lock

    override val isClosedForReceive: Boolean
        get() = lock.withLock { super.isClosedForReceive } // protected by lock

    override val isEmpty: Boolean
        get() = lock.withLock { super.isEmpty } // protected by lock
}