/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("ChannelsKt")

package kotlinx.coroutines.channels

import kotlinx.coroutines.*

/**
 * ### Deprecation note.
 *
 * This method is deprecated in the favour of [trySendBlocking].
 *
 * `sendBlocking` is considered to be dangerous primitive -- it throws
 * if the channel was closed or, more commonly, cancelled.
 * Cancellation exceptions are not ignored by non-blocking code and frequently
 * trigger internal failures.
 *
 * These bugs were hard-to-spot during code review and also forced users to write
 * their own wrappers around `sendBlocking`, so it was decided to deprecate
 * this function and provide a more explicit primitive instead.
 */
@Deprecated(
    level = DeprecationLevel.WARNING,
    message = "Deprecated in the favour of 'trySendBlocking'. " +
        "Consider handle the result of 'trySendBlocking' explicitly and rethrow exception if necessary",
    replaceWith = ReplaceWith("trySendBlocking(element)")
)
public fun <E> SendChannel<E>.sendBlocking(element: E) {
    // fast path
    if (offer(element))
        return
    // slow path
    runBlocking {
        send(element)
    }
}

/**
 * Adds [element] into to this channel, **blocking** the caller while this channel is full,
 * and returning either [successful][ChannelResult.isSuccess] result when the element was added, or
 * failed result representing closed channel with a corresponding exception.
 *
 * This is a way to call [Channel.send] method in a safe manner inside a blocking code using [runBlocking] and catching,
 * so this function should not be used from coroutine.
 *
 * Example of usage:
 * ```
 * // From callback API
 * channel.trySendBlocking(element)
 *     .onSuccess { /* request next element or debug log */ }
 *     .onFailure { t: Throwable? -> /* throw or log */ }
 *
 * ```
 * For this operation it is guaranteed that [failure][ChannelResult.failed] always contains an exception in it.
 *
 * @throws [InterruptedException] if the current thread is interrupted during the blocking send operation.
 */
public fun <E> SendChannel<E>.trySendBlocking(element: E): ChannelResult<Unit> {
    /*
     * Sent successfully -- bail out.
     * But failure may indicate either that the channel it full or that
     * it is close. Go to slow path on failure to simplify the successful path and
     * to materialize default exception.
     */
    trySend(element).onSuccess { return ChannelResult.success(Unit) }
    return runBlocking {
        val r = runCatching { send(element) }
        if (r.isSuccess) ChannelResult.success(Unit)
        else ChannelResult.closed(r.exceptionOrNull())
    }
}
