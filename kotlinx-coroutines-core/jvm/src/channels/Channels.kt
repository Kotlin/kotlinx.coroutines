/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("ChannelsKt")

package kotlinx.coroutines.channels

import kotlinx.coroutines.*

/**
 * **Deprecated** blocking variant of send.
 * This method is deprecated in the favour of [trySendBlocking].
 *
 * `sendBlocking` is a dangerous primitive &mdash; it throws an exception
 * if the channel was closed or, more commonly, cancelled.
 * Cancellation exceptions in non-blocking code are unexpected and frequently
 * trigger internal failures.
 *
 * These bugs are hard-to-spot during code review and they forced users to write
 * their own wrappers around `sendBlocking`.
 * So this function is deprecated and replaced with a more explicit primitive.
 *
 * The real-world example of broken usage with Firebase:
 *
 * ```kotlin
 * callbackFlow {
 *     val listener = object : ValueEventListener {
 *         override fun onDataChange(snapshot: DataSnapshot) {
 *             // This line may fail and crash the app when the downstream flow is cancelled
 *             sendBlocking(DataSnapshot(snapshot))
 *         }
 *
 *         override fun onCancelled(error: DatabaseError) {
 *             close(error.toException())
 *         }
 *     }
 *
 *     firebaseQuery.addValueEventListener(listener)
 *     awaitClose { firebaseQuery.removeEventListener(listener) }
 * }
 * ```
 */
@Deprecated(
    level = DeprecationLevel.WARNING,
    message = "Deprecated in the favour of 'trySendBlocking'. " +
        "Consider handling the result of 'trySendBlocking' explicitly and rethrow exception if necessary",
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
 *
 * ```
 * // From callback API
 * channel.trySendBlocking(element)
 *     .onSuccess { /* request next element or debug log */ }
 *     .onFailure { t: Throwable? -> /* throw or log */ }
 * ```
 *
 * For this operation it is guaranteed that [failure][ChannelResult.failed] always contains an exception in it.
 *
 * @throws [InterruptedException] if the current thread is interrupted during the blocking send operation.
 */
@Throws(InterruptedException::class)
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
