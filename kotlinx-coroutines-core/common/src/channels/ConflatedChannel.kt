/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.jvm.*

/**
 * Channel that buffers at most one element and conflates all subsequent `send` and `offer` invocations,
 * so that the receiver always gets the most recently sent element.
 * Back-to-send sent elements are _conflated_ -- only the the most recently sent element is received,
 * while previously sent elements **are lost**.
 * Sender to this channel never suspends and [offer] always returns `true`.
 *
 * This channel is created by `Channel(Channel.CONFLATED)` factory function invocation.
 *
 * This implementation is fully lock-free.
 */
internal open class ConflatedChannel<E>: NewAbstractChannel<E>(), Channel<E> {

}

internal abstract class NewAbstractChannel<E> : Channel<E> {
    protected abstract fun offerInternal(): Any // SUCCESS or CLOSED
    protected abstract suspend fun sendInternal(): Any // SUCCESS or CLOSED
    protected abstract fun pollInternal(): Any? // element or EMPTY or CLOSED
    protected abstract suspend fun receiveInternal(): Any? // element or EMPTY or CLOSED

    override suspend fun send(element: E) {
        val result = sendInternal()
        if (result === CLOSED_RESULT) throw sendException
    }

    override fun offer(element: E): Boolean {
        val result = offerInternal()
        when {
            result === SUCCESS_RESULT -> return true
            result === FAILED_RESULT -> return false
            result === CLOSED_RESULT -> throw sendException
            else -> error("Unexpected offerInternal invocation result: $result")
        }
    }

    override suspend fun receive(): E {
        val result = receiveInternal()
        if (result === CLOSED_RESULT) {
            throw this.receiveException
        }
        return result as E
    }

    @ObsoleteCoroutinesApi
    override suspend fun receiveOrNull(): E? {
        val result = receiveInternal()
        if (result === CLOSED_RESULT) {
            val closeCause = closeCause.value ?: return null
            throw closeCause as Throwable
        }
        return result as E
    }

    @InternalCoroutinesApi
    override suspend fun receiveOrClosed(): ValueOrClosed<E> {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun poll(): E? {
        val result = pollInternal()
        when {
            result === FAILED_RESULT -> return null
            result === CLOSED_RESULT -> {
                val closeCause = closeCause.value ?: return null
                throw closeCause as Throwable
            }
            else -> return result as (E?)
        }
    }

    // ##############################
    // ## Closing and Cancellation ##
    // ##############################

    /**
     * Indicates whether this channel is cancelled. In case it is cancelled,
     * it stores either an exception if it was cancelled with or `null` if
     * this channel was cancelled without error. Stores [NO_CLOSE_CAUSE] if this
     * channel is not cancelled.
     */
    private val closeCause = atomic<Any?>(NO_CLOSE_CAUSE)

    @Volatile
    private var closeFinished = false
    @Volatile
    private var cancelFinished = false
    @Volatile
    private var cancelled = false

    private val receiveException: Throwable
        get() = (closeCause.value as Throwable?) ?: ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE)
    private val sendException: Throwable
        get() = (closeCause.value as Throwable?) ?: ClosedSendChannelException(DEFAULT_CLOSE_MESSAGE)

    // Stores the close handler.
    private val closeHandler = atomic<Any?>(null)

    override val isClosedForSend: Boolean get() = (closeCause.value !== NO_CLOSE_CAUSE).also {
        if (it) helpCloseOrCancel()
    }

    override val isClosedForReceive: Boolean get() = isClosedForSend && isEmpty

    private fun helpCloseOrCancel() {
        if (!closeFinished) {
            helpCloseIdempotent()
            closeFinished = true
        }
        if (cancelled && !cancelFinished) {
            helpCancelIdempotent()
            cancelFinished = true
        }
    }

    /**
     * Invoked when channel is closed as the last action of [close] invocation.
     * This method should be idempotent and can be called multiple times.
     */
    protected open fun onClosed() {}

    override fun close(cause: Throwable?): Boolean {
        val closedByThisOperation = closeCause.compareAndSet(NO_CLOSE_CAUSE, cause)
        helpCloseIdempotent()
        closeFinished = true
        return if (closedByThisOperation) {
            onClosed()
            invokeCloseHandler()
            true
        } else false
    }

    private fun invokeCloseHandler() {
        val closeHandler = closeHandler.getAndUpdate {
            if (it === null) CLOSE_HANDLER_CLOSED
            else CLOSE_HANDLER_INVOKED
        } ?: return
        closeHandler as (cause: Throwable?) -> Unit
        val closeCause = closeCause.value as Throwable?
        closeHandler(closeCause)
    }

    override fun invokeOnClose(handler: (cause: Throwable?) -> Unit) {
        if (closeHandler.compareAndSet(null, handler)) {
            // Handler has been successfully set, finish the operation.
            return
        }
        // Either handler was set already or this channel is cancelled.
        // Read the value of [closeHandler] and either throw [IllegalStateException]
        // or invoke the handler respectively.
        when (val curHandler = closeHandler.value) {
            CLOSE_HANDLER_CLOSED -> {
                // In order to be sure that our handler is the only one, we have to change the
                // [closeHandler] value to `INVOKED`. If this CAS fails, another handler has been
                // executed and an [IllegalStateException] should be thrown.
                if (closeHandler.compareAndSet(CLOSE_HANDLER_CLOSED, CLOSE_HANDLER_INVOKED)) {
                    handler(closeCause.value as Throwable?)
                } else {
                    throw IllegalStateException("Another handler was already registered and successfully invoked")
                }
            }
            CLOSE_HANDLER_INVOKED -> error("Another handler was already registered and successfully invoked")
            else -> error("Another handler was already registered: $curHandler")
        }
    }

    final override fun cancel(cause: Throwable?): Boolean = cancelImpl(cause)
    final override fun cancel() { cancelImpl(null) }
    final override fun cancel(cause: CancellationException?) { cancelImpl(cause) }

    protected open fun cancelImpl(cause: Throwable?): Boolean {
        cancelled = true
        val closedByThisOperation = close(cause)
        helpCancelIdempotent()
        cancelFinished = true
        return closedByThisOperation
    }

    protected abstract fun helpCloseIdempotent()
    protected abstract fun helpCancelIdempotent()

    // ######################
    // ## Iterator Support ##
    // ######################

    override fun iterator(): ChannelIterator<E> = object : ChannelIterator<E> {
        private var result: Any? = NO_RESULT // NO_RESULT | E (next element) | CLOSED
        override suspend fun hasNext(): Boolean {
            if (result != NO_RESULT) return checkNotClosed(result)
            // Try to receive an element. Store the result even if
            // receiving fails in order to process further [hasNext]
            // and [next] invocations properly.
            result = receiveInternal() // todo: tail call optimization?
            return if (result == CLOSED_RESULT) {
                if (closeCause.value == null) {
                    false
                } else {
                    throw (closeCause.value as Throwable)
                }
            } else true
        }

        private fun checkNotClosed(result: Any?): Boolean {
            return if (result === CLOSED_RESULT) {
                if (closeCause.value != null) throw (closeCause.value as Throwable)
                false
            } else true
        }

        @Suppress("UNCHECKED_CAST")
        override fun next(): E =
            // Read the already received result or NO_RESULT if [hasNext] has not been invoked yet.
            when (val result = this.result) {
                // Rare case -- [hasNext] has not been invoked, invoke [receive] directly.
                NO_RESULT -> error("[hasNext] has not been invoked")
                // Channel is closed, throw the cause exception.
                CLOSED_RESULT -> throw receiveException
                // An element has been received successfully.
                else -> {
                    // Reset the [result] field and return the element.
                    this.result = NO_RESULT
                    result as E
                }
            }
    }
}

// Special values for `CLOSE_HANDLER`
private val CLOSE_HANDLER_CLOSED = Symbol("CLOSE_HANDLER_CLOSED")
private val CLOSE_HANDLER_INVOKED = Symbol("CLOSE_HANDLER_INVOKED")
// Specifies the absence of the close cause
private val NO_CLOSE_CAUSE = Symbol("NO_CLOSE_CAUSE")

// Special return values
private val NO_RESULT = Symbol("NO_RESULT")
internal val SUCCESS_RESULT = Symbol("SUCCESS_RESULT")
internal val FAILED_RESULT = Symbol("FAILED_RESULT")
internal val CLOSED_RESULT = Symbol("CLOSED_RESULT")