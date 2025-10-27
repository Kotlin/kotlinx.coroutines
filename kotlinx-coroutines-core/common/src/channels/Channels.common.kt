@file:JvmMultifileClass
@file:JvmName("ChannelsKt")
@file:OptIn(ExperimentalContracts::class)

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.consumeAsFlow
import kotlinx.coroutines.flow.toCollection
import kotlinx.coroutines.flow.toList
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
 * Executes the [block] and then [cancels][ReceiveChannel.cancel] the channel.
 *
 * It is guaranteed that, after invoking this operation, the channel will be [cancelled][ReceiveChannel.cancel], so
 * the operation is _terminal_.
 * If the [block] finishes with an exception, that exception will be used for cancelling the channel and rethrown.
 *
 * This function is useful for building more complex terminal operators while ensuring that the producers stop sending
 * new elements to the channel.
 *
 * Example:
 * ```
 * suspend fun <E> ReceiveChannel<E>.consumeFirst(): E =
 *    consume { return receive() }
 * // Launch a coroutine that constantly sends new values
 * val channel = produce(Dispatchers.Default) {
 *     var i = 0
 *     while (true) {
 *         // Will fail with a `CancellationException`
 *         // after `consumeFirst` finishes.
 *         send(i++)
 *     }
 * }
 * // Grab the first value and discard everything else
 * val firstElement = channel.consumeFirst()
 * check(firstElement == 0)
 * // *Note*: some elements could be lost in the channel!
 * ```
 *
 * In this example, the channel will get closed, and the producer coroutine will finish its work after the first
 * element is obtained.
 * If `consumeFirst` was implemented as `for (e in this) { return e }` instead, the producer coroutine would be active
 * until it was cancelled some other way.
 *
 * [consume] does not guarantee that new elements will not enter the channel after [block] finishes executing, so
 * some channel elements may be lost.
 * Use the `onUndeliveredElement` parameter of a manually created [Channel] to define what should happen with these
 * elements during [ReceiveChannel.cancel].
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
 * This function stops processing elements when either the channel is [closed][SendChannel.close],
 * the coroutine in which the collection is performed gets cancelled and there are no readily available elements in the
 * channel's buffer,
 * [action] fails with an exception,
 * or an early return from [action] happens.
 * If the [action] finishes with an exception, that exception will be used for cancelling the channel and rethrown.
 * If the channel is [closed][SendChannel.close] with a cause, this cause will be rethrown from [consumeEach].
 *
 * When the channel does not need to be closed after iterating over its elements,
 * a regular `for` loop (`for (element in channel)`) should be used instead.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] the elements of the original [ReceiveChannel].
 *
 * This function is useful in cases when this channel is only expected to have a single consumer that decides when
 * the producer may stop.
 * Example:
 *
 * ```
 * val channel = Channel<Int>(1)
 * // Launch several procedures that create values
 * repeat(5) {
 *     launch(Dispatchers.Default) {
 *         while (true) {
 *             channel.send(Random.nextInt(40, 50))
 *         }
 *     }
 * }
 * // Launch the exclusive consumer
 * val result = run {
 *     channel.consumeEach {
 *         if (it == 42) {
 *             println("Found the answer")
 *             return@run it // forcibly stop collection
 *         }
 *     }
 *     // *Note*: some elements could be lost in the channel!
 * }
 * check(result == 42)
 * ```
 *
 * In this example, several coroutines put elements into a single channel, and a single consumer processes the elements.
 * Once it finds the elements it's looking for, it stops [consumeEach] by making an early return.
 *
 * **Pitfall**: even though the name says "each", some elements could be left unprocessed if they are added after
 * this function decided to close the channel.
 * In this case, the elements will simply be lost.
 * If the elements of the channel are resources that must be closed (like file handles, sockets, etc.),
 * an `onUndeliveredElement` must be passed to the [Channel] on construction.
 * It will be called for each element left in the channel at the point of cancellation.
 */
public suspend inline fun <E> ReceiveChannel<E>.consumeEach(action: (E) -> Unit): Unit =
    consume {
        for (e in this) action(e)
    }

/**
 * [Consumes][consume] the elements of this channel into a list, preserving their order.
 *
 * This is a convenience function equivalent to calling [consumeAsFlow] followed by [kotlinx.coroutines.flow.toList].
 * It is useful for testing code that uses channels to observe the elements the channel contains at the end of the test.
 *
 * There is no way to recover channel elements if the channel gets closed with an exception
 * or to apply additional transformations to the elements before building the resulting collection.
 * Please use [consumeAsFlow] and [kotlinx.coroutines.flow.toCollection] for such advanced use-cases.
 *
 * [toList] attempts to receive elements and put them into the list until the channel is
 * [closed][SendChannel.close].
 * Calling [toList] on channels that are not eventually closed is always incorrect:
 * - It will suspend indefinitely if the channel is not closed, but no new elements arrive.
 * - If new elements do arrive and the channel is not eventually closed, [toList] will use more and more memory
 *   until exhausting it.
 *
 * If the channel is [closed][SendChannel.close] with a cause, [toList] will rethrow that cause.
 *
 * Since this function is implemented using [consume], it is _terminal_,
 * meaning that [toList] will [cancel][ReceiveChannel.cancel] the channel before exiting.
 * A [toList] call can finish before the sender closes the channel
 * if it gets cancelled while waiting for the next element,
 * or if [MutableList.add] fails with an exception.
 * In both cases, the exception will be used for cancelling the channel and then rethrown.
 *
 * Example:
 * ```
 * val values = listOf(1, 5, 2, 9, 3, 3, 1)
 * // start a new coroutine that creates a channel,
 * // sends elements to it, and closes it
 * // once the coroutine's body finishes
 * val channel = produce {
 *     values.forEach { send(it) }
 * }
 * check(channel.toList() == values)
 * ```
 */
public suspend fun <E> ReceiveChannel<E>.toList(): List<E> = buildList {
    consumeEach(::add)
}

/**
 * [Consumes][consume] the elements of this channel into the provided mutable collection.
 *
 * This is a convenience function equivalent to calling [consumeAsFlow]
 * followed by [kotlinx.coroutines.flow.toCollection].
 * Please use [consumeAsFlow] directly in scenarios where elements should undergo additional transformations
 * before being added to the resulting collection.
 *
 * [consumeTo] attempts to receive elements and put them into the collection until the channel is
 * [closed][SendChannel.close].
 *
 * If the channel is [closed][SendChannel.close] with a cause, [consumeTo] will rethrow that cause.
 * However, the elements already received up to that point will remain in the collection.
 *
 * Since this function is implemented using [consume], it is _terminal_,
 * meaning that [consumeTo] will [cancel][ReceiveChannel.cancel] the channel before exiting.
 * A [consumeTo] call can finish before the sender closes the channel
 * if it gets cancelled while waiting for the next element,
 * or if [MutableCollection.add] fails with an exception.
 * In both cases, the exception will be used for cancelling the channel and then rethrown.
 *
 * The intended use case for this function is collecting the remaining elements of a closed channel
 * and processing them in a single batch.
 *
 * Example:
 * ```
 * val doContinue = AtomicBoolean(true)
 *
 * // Start the sender
 * val channel = produce {
 *     var i = 0
 *     while (doContinue.load()) {
 *         send(i++)
 *         delay(10.milliseconds)
 *         if (i == 42) break
 *     }
 * }
 *
 * // Start the consumer
 * launch {
 *     // Read elements until we suddenly decide to stop
 *     // or until the channel is closed.
 *     while (Random.nextInt() % 100 != 0) {
 *         val nextElement = channel.receiveCatching()
 *         if (nextElement.isClosed) return@launch
 *         println("Received ${nextElement.getOrNull()}")
 *     }
 *     delay(100.milliseconds)
 *     doContinue.store(false)
 *     delay(100.milliseconds)
 *     val remainingElements = mutableListOf<Int>()
 *     try {
 *         channel.consumeTo(remainingElements)
 *     } finally {
 *         println("Remaining elements: $remainingElements")
 *     }
 * }
 * ```
 */
public suspend fun <E, C: MutableCollection<E>> ReceiveChannel<E>.consumeTo(collection: C): C =
    consumeEach(collection::add).let { collection }


@PublishedApi
internal fun ReceiveChannel<*>.cancelConsumed(cause: Throwable?) {
    cancel(cause?.let {
        it as? CancellationException ?: CancellationException("Channel was consumed, consumer had failed", it)
    })
}

