/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
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
 * Opens subscription to this [BroadcastChannel] and makes sure that the given [block] consumes all elements
 * from it by always invoking [cancel][ReceiveChannel.cancel] after the execution of the block.
 *
 * **Note: This API is obsolete since 1.5.0 and deprecated for removal since 1.7.0**
 * It is replaced with [SharedFlow][kotlinx.coroutines.flow.SharedFlow].
 *
 * Safe to remove in 1.9.0 as was inline before.
 */
@ObsoleteCoroutinesApi
@Suppress("DEPRECATION")
@Deprecated(level = DeprecationLevel.WARNING, message = "BroadcastChannel is deprecated in the favour of SharedFlow and is no longer supported")
public inline fun <E, R> BroadcastChannel<E>.consume(block: ReceiveChannel<E>.() -> R): R {
    val channel = openSubscription()
    try {
        return channel.block()
    } finally {
        channel.cancel()
    }
}

/**
 * This function is deprecated in the favour of [ReceiveChannel.receiveCatching].
 *
 * This function is considered error-prone for the following reasons;
 * * Is throwing if the channel has failed even though its signature may suggest it returns 'null'
 * * It is easy to forget that exception handling still have to be explicit
 * * During code reviews and code reading, intentions of the code are frequently unclear:
 *   are potential exceptions ignored deliberately or not?
 *
 * @suppress doc
 */
@Deprecated(
    "Deprecated in the favour of 'receiveCatching'",
    ReplaceWith("receiveCatching().getOrNull()"),
    DeprecationLevel.ERROR
) // Warning since 1.5.0, ERROR in 1.6.0, HIDDEN in 1.7.0
@Suppress("EXTENSION_SHADOWED_BY_MEMBER", "DEPRECATION_ERROR")
public suspend fun <E : Any> ReceiveChannel<E>.receiveOrNull(): E? {
    return (this as ReceiveChannel<E?>).receiveOrNull()
}

/**
 * This function is deprecated in the favour of [ReceiveChannel.onReceiveCatching]
 */
@Deprecated(
    "Deprecated in the favour of 'onReceiveCatching'",
    level = DeprecationLevel.ERROR
)  // Warning since 1.5.0, ERROR in 1.6.0, HIDDEN in 1.7.0
@Suppress("DEPRECATION_ERROR")
public fun <E : Any> ReceiveChannel<E>.onReceiveOrNull(): SelectClause1<E?> {
    return (this as ReceiveChannel<E?>).onReceiveOrNull
}

/**
 * Makes sure that the given [block] consumes all elements from the given channel
 * by always invoking [cancel][ReceiveChannel.cancel] after the execution of the block.
 *
 * The operation is _terminal_.
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
 * Performs the given [action] for each received element and [cancels][ReceiveChannel.cancel]
 * the channel after the execution of the block.
 * If you need to iterate over the channel without consuming it, a regular `for` loop should be used instead.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.consumeEach(action: (E) -> Unit): Unit =
    consume {
        for (e in this) action(e)
    }

/**
 * Returns a [List] containing all elements.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.toList(): List<E> = buildList {
    consumeEach {
        add(it)
    }
}

/**
 * Subscribes to this [BroadcastChannel] and performs the specified action for each received element.
 *
 * **Note: This API is obsolete since 1.5.0 and deprecated for removal since 1.7.0**
 */
@Deprecated(level = DeprecationLevel.WARNING, message = "BroadcastChannel is deprecated in the favour of SharedFlow and is no longer supported")
@Suppress("DEPRECATION")
public suspend inline fun <E> BroadcastChannel<E>.consumeEach(action: (E) -> Unit): Unit =
    consume {
        for (element in this) action(element)
    }


@PublishedApi
internal fun ReceiveChannel<*>.cancelConsumed(cause: Throwable?) {
    cancel(cause?.let {
        it as? CancellationException ?: CancellationException("Channel was consumed, consumer had failed", it)
    })
}

