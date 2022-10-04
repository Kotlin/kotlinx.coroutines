@file:JvmMultifileClass
@file:JvmName("ChannelsKt")

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.jvm.*

/**
 * Adds [element] to this channel, **blocking** the caller while this channel is full,
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
 * @throws `InterruptedException` on JVM if the current thread is interrupted during the blocking send operation.
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

/** @suppress */
@Deprecated(
    level = DeprecationLevel.ERROR,
    message = "Deprecated in the favour of 'trySendBlocking'. " +
        "Consider handling the result of 'trySendBlocking' explicitly and rethrow exception if necessary",
    replaceWith = ReplaceWith("trySendBlocking(element)")
) // WARNING in 1.5.0, ERROR in 1.6.0, HIDDEN in 1.7.0
public fun <E> SendChannel<E>.sendBlocking(element: E) {
    // fast path
    if (trySend(element).isSuccess)
        return
    // slow path
    runBlocking {
        send(element)
    }
}
