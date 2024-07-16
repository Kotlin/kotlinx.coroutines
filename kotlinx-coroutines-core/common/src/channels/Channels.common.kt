@file:JvmMultifileClass
@file:JvmName("ChannelsKt")
@file:OptIn(ExperimentalContracts::class)

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import kotlin.contracts.*
import kotlin.jvm.*

internal const val DEFAULT_CLOSE_MESSAGE = "Channel was closed"


// -------- Operations on BroadcastChannel --------

/**
 * This function is deprecated in the favour of [ReceiveChannel.receiveCatching].
 *
 * This function is considered error-prone for the following reasons;
 * - Is throwing if the channel has failed even though its signature may suggest it returns 'null'
 * - It is easy to forget that exception handling still have to be explicit
 * - During code reviews and code reading, intentions of the code are frequently unclear:
 *   are potential exceptions ignored deliberately or not?
 *
 * @suppress doc
 */
@Deprecated(
    "Deprecated in the favour of 'receiveCatching'",
    ReplaceWith("receiveCatching().getOrNull()"),
    DeprecationLevel.HIDDEN
) // Warning since 1.5.0, ERROR in 1.6.0, HIDDEN in 1.7.0
@Suppress("EXTENSION_SHADOWED_BY_MEMBER", "DEPRECATION_ERROR")
public suspend fun <E : Any> ReceiveChannel<E>.receiveOrNull(): E? {
    @Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
    return (this as ReceiveChannel<E?>).receiveOrNull()
}

/**
 * This function is deprecated in the favour of [ReceiveChannel.onReceiveCatching]
 */
@Deprecated(
    "Deprecated in the favour of 'onReceiveCatching'",
    level = DeprecationLevel.HIDDEN
)  // Warning since 1.5.0, ERROR in 1.6.0, HIDDEN in 1.7.0
@Suppress("DEPRECATION_ERROR")
public fun <E : Any> ReceiveChannel<E>.onReceiveOrNull(): SelectClause1<E?> {
    return (this as ReceiveChannel<E?>).onReceiveOrNull
}

/**
 * Executes the [block] and then [cancels][ReceiveChannel.cancel] the channel,
 * ensuring that all the elements that were sent are processed by either [block] or [ReceiveChannel.cancel].
 *
 * It is guaranteed that, after invoking this operation, the channel will be [cancelled][ReceiveChannel.cancel], so
 * the operation is _terminal_.
 * If the [block] finishes with an exception, that exception will be used for cancelling the channel.
 *
 * This function is useful for building more complex terminal operators while ensuring that no elements will be lost.
 * Example:
 *
 * ```
 * suspend fun <E> ReceiveChannel<E>.consumeFirst(): E =
 *     consume { return receive() }
 * 
 * fun Int.cleanup() { println("cleaning up $this") }
 *
 * val channel = Channel<Int>(10, onUndeliveredElement = Int::cleanup)
 * // Launch a procedure that creates values
 * launch(Dispatchers.Default) {
 *     repeat(10) {
 *         val sendResult = channel.trySend(it)
 *         if (sendResult.isFailure) {
 *             print("in the producer: ")
 *             it.cleanup()
 *         }
 *         yield()
 *     }
 * }
 * // Grab the first value and discard everything else
 * launch(Dispatchers.Default) {
 *     val firstElement = channel.consumeFirst()
 *     println("received $firstElement")
 * }
 * ```
 *
 * In this example, all ten values created by the producer coroutine will be processed: one by `consumeFirst`,
 * and the other ones by `Int.cleanup`, invoked either by [ReceiveChannel.cancel] inside [consume] or by the
 * producer itself when it observes failure.
 * In any case, exactly nine elements will go through a cleanup in this example.
 * If `consumeFirst` is implemented as `for (e in this) { return e }` instead, the cleanup does not happen.
 */
public inline fun <E, R> ReceiveChannel<E>.consume(block: ReceiveChannel<E>.() -> R): R {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    var cause: Throwable? = null
    try {
        return block()
    } catch (e: Throwable) {
        cause = e
        throw e
    } finally {
        cancelConsumed(cause)
    }
}

/**
 * Performs the given [action] for each received element and [cancels][ReceiveChannel.cancel] the channel afterward.
 *
 * This function stops processing elements when the channel is [closed][SendChannel.close],
 * the coroutine in which the collection is performed gets cancelled and there are no readily available elements in the
 * channel's buffer,
 * or an early return from [action] happens.
 * If the [action] finishes with an exception, that exception will be used for cancelling the channel and rethrown.
 * If the channel is [closed][SendChannel.close] with a cause, this cause will be rethrown from [consumeEach].
 *
 * When the channel does not need to be closed after iterating over its elements,
 * a regular `for` loop (`for (element in channel)`) should be used instead.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 *
 * This function is useful in cases when this channel is only expected to have a single consumer that decides when
 * the producer may stop and ensures that the elements that were sent do get processed.
 * Example:
 *
 * ```
 * fun Int.cleanup() { println("cleaning up $this") }
 * val channel = Channel<Int>(1, onUndeliveredElement = Int::cleanup)
 * // Launch several procedures that create values
 * repeat(5) {
 *     launch(Dispatchers.Default) {
 *         while (true) {
 *             val x = Random.nextInt(40, 50)
 *             println("Generating $x")
 *             channel.send(x)
 *         }
 *     }
 * }
 * // Launch the exclusive consumer
 * launch(Dispatchers.Default) {
 *     channel.consumeEach {
 *         if (it == 42) {
 *             println("Found the answer")
 *             return@launch
 *         } else {
 *             it.cleanup()
 *         }
 *     }
 * }
 * ```
 *
 * In this example, all ten values created by the producer coroutines will be processed:
 * while the single consumer is active, it will receive all the elements, but once it exits,
 * the values that can no longer be delivered will be passed to the `Int.cleanup` handler.
 */
public suspend inline fun <E> ReceiveChannel<E>.consumeEach(action: (E) -> Unit): Unit =
    consume {
        for (e in this) action(e)
    }

/**
 * Returns a [List] containing all the elements sent to this channel, preserving their order.
 *
 * This function will attempt to receive elements and put them into the list until the channel is
 * [closed][SendChannel.close].
 * Calling [toList] without closing the channel is always incorrect:
 * - It will suspend indefinitely if the channel is not closed, but no new elements arrive.
 * - If new elements do arrive and the channel is not eventually closed, [toList] will use more and more memory
 *   until exhausting it.
 *
 * If the channel is [closed][SendChannel.close] with a cause, [toList] will rethrow that cause.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 *
 * Example:
 * ```
 * val values = listOf(1, 5, 2, 9, 3, 3, 1)
 * val channel = Channel<Int>()
 * GlobalScope.launch {
 *     values.forEach { channel.send(it) }
 *     channel.close()
 * }
 * check(channel.toList() == values)
 * ```
 */
public suspend fun <E> ReceiveChannel<E>.toList(): List<E> = buildList {
    consumeEach {
        add(it)
    }
}

@PublishedApi
internal fun ReceiveChannel<*>.cancelConsumed(cause: Throwable?) {
    cancel(cause?.let {
        it as? CancellationException ?: CancellationException("Channel was consumed, consumer had failed", it)
    })
}

