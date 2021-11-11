/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.internal.recoverStackTrace
import kotlin.jvm.*

/**
 * Returns a new iterator to receive elements from this channel using a `for` loop.
 * Iteration completes normally when the channel [is closed for `receive`][isClosedForReceive] without a cause and
 * throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
 */
@Suppress("EXTENSION_SHADOWED_BY_MEMBER") // NOT shadowed -- member is HIDDEN
public operator fun <E> ReceiveChannel<E>.iterator(): ChannelIterator<E> = ChannelIteratorImpl(this)

/**
 * Iterator for [ReceiveChannel]. Instances of this interface are *not thread-safe* and shall not be used
 * from concurrent coroutines.
 */
public interface ChannelIterator<out E> {
    /**
     * Returns `true` if the channel has more elements, suspending the caller while this channel is empty,
     * or returns `false` if the channel [is closed for `receive`][ReceiveChannel.isClosedForReceive] without a cause.
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     *
     * This function retrieves and removes an element from this channel for the subsequent invocation
     * of [next].
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with a [CancellationException].
     * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
     * suspended, it will not resume successfully. The `hasNext` call can retrieve the element from the channel,
     * but then throw [CancellationException], thus failing to deliver the element.
     * See "Undelivered elements" section in [Channel] documentation for details on handling undelivered elements.
     *
     * Note that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     */
    public suspend operator fun hasNext(): Boolean

    @Deprecated(message = "Since 1.3.0, binary compatibility with versions <= 1.2.x", level = DeprecationLevel.HIDDEN)
    @Suppress("INAPPLICABLE_JVM_NAME")
    @JvmName("next")
    public suspend fun next0(): E {
        /*
         * Before 1.3.0 the "next()" could have been used without invoking "hasNext" first and there were code samples
         * demonstrating this behavior, so we preserve this logic for full binary backwards compatibility with previously
         * compiled code.
         */
        if (!hasNext()) throw ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE)
        return next()
    }

    /**
     * Retrieves the element removed from the channel by a preceding call to [hasNext], or
     * throws an [IllegalStateException] if [hasNext] was not invoked.
     * This method should only be used in pair with [hasNext]:
     * ```
     * while (iterator.hasNext()) {
     *     val element = iterator.next()
     *     // ... handle element ...
     * }
     * ```
     *
     * This method throws a [ClosedReceiveChannelException] if the channel [is closed for `receive`][ReceiveChannel.isClosedForReceive] without a cause.
     * It throws the original [close][SendChannel.close] cause exception if the channel has _failed_.
     */
    public operator fun next(): E
}

private class ChannelIteratorImpl<E>(val c: ReceiveChannel<E>): ChannelIterator<E> {
    private var receiveResult: ChannelResult<E>? = null
    override suspend fun hasNext(): Boolean {
        // Try to receive the next element if required.
        if (receiveResult == null) {
            val receiveResult = c.tryReceive()
            receiveResult.onSuccess {
                this.receiveResult = receiveResult
                return true
            }.onClosed { cause ->
                this.receiveResult = receiveResult
                if (cause == null) return false
                else throw recoverStackTrace(cause)
            }
        }
        // The operation is likely to suspend, go to the slow-path.
        return hasNextSuspend()
    }

    private suspend fun hasNextSuspend(): Boolean {
        this.receiveResult = c.receiveCatching()
        receiveResult!!.let {
            it.onSuccess { return true }
            it.onClosed { cause ->
                if (cause == null) return false
                else throw recoverStackTrace(cause)
            }
        }
        error("unreachable")
    }

    @Suppress("UNCHECKED_CAST")
    override fun next(): E {
        // Read the already received result, or null if [hasNext] has not been invoked yet.
        val result = this.receiveResult ?: error("`hasNext()` has not been invoked")
        result.onSuccess { element ->
            this.receiveResult = null
            return element
        }.onFailure { cause ->
            throw recoverStackTrace(cause.receiveException)
        }
        error("unreachable")
    }
}