/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

internal const val DEFAULT_CLOSE_MESSAGE = "Channel was closed"


// -------- Conversions to ReceiveChannel  --------

/**
 * Returns a channel to read all element of the [Iterable].
 */
public fun <E> Iterable<E>.asReceiveChannel(context: CoroutineContext = Unconfined): ReceiveChannel<E> =
    produce(context) {
        for (element in this@asReceiveChannel)
            send(element)
    }

/**
 * Returns a channel to read all element of the [Sequence].
 */
public fun <E> Sequence<E>.asReceiveChannel(context: CoroutineContext = Unconfined): ReceiveChannel<E> =
    produce(context) {
        for (element in this@asReceiveChannel)
            send(element)
    }

// -------- Operations on BroadcastChannel --------

/**
 * Opens subscription to this [BroadcastChannel] and makes sure that the given [block] consumes all elements
 * from it by always invoking [cancel][SubscriptionReceiveChannel.cancel] after the execution of the block.
 */
public inline fun <E, R> BroadcastChannel<E>.consume(block: SubscriptionReceiveChannel<E>.() -> R): R {
    val channel = openSubscription()
    try {
        return channel.block()
    } finally {
        channel.cancel()
    }
}

/**
 * Subscribes to this [BroadcastChannel] and performs the specified action for each received element.
 */
public suspend inline fun <E> BroadcastChannel<E>.consumeEach(action: (E) -> Unit) =
    consume {
        for (element in this) action(element)
    }

/**
 * @suppress: **Deprecated**: binary compatibility with old code
 */
@Deprecated("binary compatibility with old code", level = DeprecationLevel.HIDDEN)
public suspend fun <E> BroadcastChannel<E>.consumeEach(action: suspend (E) -> Unit) =
    consumeEach { action(it) }

// -------- Operations on ReceiveChannel --------

/**
 * Returns a [CompletionHandler] that invokes [cancel][ReceiveChannel.cancel] on the [ReceiveChannel]
 * with the corresponding cause. See also [ReceiveChannel.consume].
 *
 * **WARNING**: It is planned that in the future a second invocation of this method
 * on an channel that is already being consumed is going to fail fast, that is
 * immediately throw an [IllegalStateException].
 * See [this issue](https://github.com/Kotlin/kotlinx.coroutines/issues/167)
 * for details.
 */
public fun ReceiveChannel<*>.consumes(): CompletionHandler =
    { cause: Throwable? -> cancel(cause) }

/**
 * Returns a [CompletionHandler] that invokes [cancel][ReceiveChannel.cancel] on all the
 * specified [ReceiveChannel] instances with the corresponding cause.
 * See also [ReceiveChannel.consumes()] for a version on one channel.
 */
public fun consumesAll(vararg channels: ReceiveChannel<*>): CompletionHandler =
    { cause: Throwable? ->
        var exception: Throwable? = null
        for (channel in channels)
            try {
                channel.cancel(cause)
            } catch (e: Throwable) {
                if (exception == null) {
                    exception = e
                } else {
                    exception.addSuppressedThrowable(e)
                }
            }
        exception?.let { throw it }
    }

/**
 * Makes sure that the given [block] consumes all elements from the given channel
 * by always invoking [cancel][ReceiveChannel.cancel] after the execution of the block.
 *
 * **WARNING**: It is planned that in the future a second invocation of this method
 * on an channel that is already being consumed is going to fail fast, that is
 * immediately throw an [IllegalStateException].
 * See [this issue](https://github.com/Kotlin/kotlinx.coroutines/issues/167)
 * for details.
 *
 * The operation is _terminal_.
 */
public inline fun <E, R> ReceiveChannel<E>.consume(block: ReceiveChannel<E>.() -> R): R {
    var cause: Throwable? = null
    try {
        return block()
    } catch (e: Throwable) {
        cause = e
        throw e
    } finally {
        cancel(cause)
    }
}

/**
 * Performs the given [action] for each received element.
 *
 * **WARNING**: It is planned that in the future a second invocation of this method
 * on an channel that is already being consumed is going to fail fast, that is
 * immediately throw an [IllegalStateException].
 * See [this issue](https://github.com/Kotlin/kotlinx.coroutines/issues/167)
 * for details.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.consumeEach(action: (E) -> Unit) =
    consume {
        for (e in this) action(e)
    }

/**
 * @suppress: **Deprecated**: binary compatibility with old code
 */
@Deprecated("binary compatibility with old code", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.consumeEach(action: suspend (E) -> Unit) =
    consumeEach { action(it) }

/**
 * Performs the given [action] for each received element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.consumeEachIndexed(action: (IndexedValue<E>) -> Unit) {
    var index = 0
    consumeEach {
        action(IndexedValue(index++, it))
    }
}

/**
 * Returns an element at the given [index] or throws an [IndexOutOfBoundsException] if the [index] is out of bounds of this channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.elementAt(index: Int): E =
    elementAtOrElse(index) { throw IndexOutOfBoundsException("ReceiveChannel doesn't contain element at index $index.") }

/**
 * Returns an element at the given [index] or the result of calling the [defaultValue] function if the [index] is out of bounds of this channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.elementAtOrElse(index: Int, defaultValue: (Int) -> E): E =
    consume {
        if (index < 0)
            return defaultValue(index)
        var count = 0
        for (element in this) {
            if (index == count++)
                return element
        }
        return defaultValue(index)
    }

/**
 * Returns an element at the given [index] or `null` if the [index] is out of bounds of this channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.elementAtOrNull(index: Int): E? =
    consume {
        if (index < 0)
            return null
        var count = 0
        for (element in this) {
            if (index == count++)
                return element
        }
        return null
    }

/**
 * Returns the first element matching the given [predicate], or `null` if no such element was found.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.find(predicate: (E) -> Boolean): E? =
    firstOrNull(predicate)

/**
 * Returns the last element matching the given [predicate], or `null` if no such element was found.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.findLast(predicate: (E) -> Boolean): E? =
    lastOrNull(predicate)

/**
 * Returns first element.
 * @throws [NoSuchElementException] if the channel is empty.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.first(): E =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext())
            throw NoSuchElementException("ReceiveChannel is empty.")
        return iterator.next()
    }

/**
 * Returns the first element matching the given [predicate].
 * @throws [NoSuchElementException] if no such element is found.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.first(predicate: (E) -> Boolean): E {
    consumeEach {
        if (predicate(it)) return it
    }
    throw NoSuchElementException("ReceiveChannel contains no element matching the predicate.")
}

/**
 * Returns the first element, or `null` if the channel is empty.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.firstOrNull(): E? =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext())
            return null
        return iterator.next()
    }

/**
 * Returns the first element matching the given [predicate], or `null` if element was not found.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public inline suspend fun <E> ReceiveChannel<E>.firstOrNull(predicate: (E) -> Boolean): E? {
    consumeEach {
        if (predicate(it)) return it
    }
    return null
}

/**
 * Returns first index of [element], or -1 if the channel does not contain element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.indexOf(element: E): Int {
    var index = 0
    consumeEach {
        if (element == it)
            return index
        index++
    }
    return -1
}

/**
 * Returns index of the first element matching the given [predicate], or -1 if the channel does not contain such element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.indexOfFirst(predicate: (E) -> Boolean): Int {
    var index = 0
    consumeEach {
        if (predicate(it))
            return index
        index++
    }
    return -1
}

/**
 * Returns index of the last element matching the given [predicate], or -1 if the channel does not contain such element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public inline suspend fun <E> ReceiveChannel<E>.indexOfLast(predicate: (E) -> Boolean): Int {
    var lastIndex = -1
    var index = 0
    consumeEach {
        if (predicate(it))
            lastIndex = index
        index++
    }
    return lastIndex
}

/**
 * Returns the last element.
 * @throws [NoSuchElementException] if the channel is empty.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.last(): E =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext())
            throw NoSuchElementException("ReceiveChannel is empty.")
        var last = iterator.next()
        while (iterator.hasNext())
            last = iterator.next()
        return last
    }

/**
 * Returns the last element matching the given [predicate].
 * @throws [NoSuchElementException] if no such element is found.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.last(predicate: (E) -> Boolean): E {
    var last: E? = null
    var found = false
    consumeEach {
        if (predicate(it)) {
            last = it
            found = true
        }
    }
    if (!found) throw NoSuchElementException("ReceiveChannel contains no element matching the predicate.")
    @Suppress("UNCHECKED_CAST")
    return last as E
}

/**
 * Returns last index of [element], or -1 if the channel does not contain element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.lastIndexOf(element: E): Int {
    var lastIndex = -1
    var index = 0
    consumeEach {
        if (element == it)
            lastIndex = index
        index++
    }
    return lastIndex
}

/**
 * Returns the last element, or `null` if the channel is empty.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.lastOrNull(): E? =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext())
            return null
        var last = iterator.next()
        while (iterator.hasNext())
            last = iterator.next()
        return last
    }

/**
 * Returns the last element matching the given [predicate], or `null` if no such element was found.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.lastOrNull(predicate: (E) -> Boolean): E? {
    var last: E? = null
    consumeEach {
        if (predicate(it)) {
            last = it
        }
    }
    return last
}

/**
 * Returns the single element, or throws an exception if the channel is empty or has more than one element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.single(): E =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext())
            throw NoSuchElementException("ReceiveChannel is empty.")
        val single = iterator.next()
        if (iterator.hasNext())
            throw IllegalArgumentException("ReceiveChannel has more than one element.")
        return single
    }

/**
 * Returns the single element matching the given [predicate], or throws exception if there is no or more than one matching element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.single(predicate: (E) -> Boolean): E {
    var single: E? = null
    var found = false
    consumeEach {
        if (predicate(it)) {
            if (found) throw IllegalArgumentException("ReceiveChannel contains more than one matching element.")
            single = it
            found = true
        }
    }
    if (!found) throw NoSuchElementException("ReceiveChannel contains no element matching the predicate.")
    @Suppress("UNCHECKED_CAST")
    return single as E
}

/**
 * Returns single element, or `null` if the channel is empty or has more than one element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.singleOrNull(): E? =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext())
            return null
        val single = iterator.next()
        if (iterator.hasNext())
            return null
        return single
    }

/**
 * Returns the single element matching the given [predicate], or `null` if element was not found or more than one element was found.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.singleOrNull(predicate: (E) -> Boolean): E? {
    var single: E? = null
    var found = false
    consumeEach {
        if (predicate(it)) {
            if (found) return null
            single = it
            found = true
        }
    }
    if (!found) return null
    return single
}

/**
 * Returns a channel containing all elements except first [n] elements.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public fun <E> ReceiveChannel<E>.drop(n: Int, context: CoroutineContext = Unconfined): ReceiveChannel<E> =
    produce(context, onCompletion = consumes()) {
        require(n >= 0) { "Requested element count $n is less than zero." }
        var remaining: Int = n
        if (remaining > 0)
            for (e in this@drop) {
                remaining--
                if (remaining == 0)
                    break
            }
        for (e in this@drop) {
            send(e)
        }
    }

/**
 * Returns a channel containing all elements except first elements that satisfy the given [predicate].
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
// todo: mark predicate with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public fun <E> ReceiveChannel<E>.dropWhile(context: CoroutineContext = Unconfined, predicate: suspend (E) -> Boolean): ReceiveChannel<E> =
    produce(context, onCompletion = consumes()) {
        for (e in this@dropWhile) {
            if (!predicate(e)) {
                send(e)
                break
            }
        }
        for (e in this@dropWhile) {
            send(e)
        }
    }

/**
 * Returns a channel containing only elements matching the given [predicate].
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
// todo: mark predicate with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public fun <E> ReceiveChannel<E>.filter(context: CoroutineContext = Unconfined, predicate: suspend (E) -> Boolean): ReceiveChannel<E> =
    produce(context, onCompletion = consumes()) {
        for (e in this@filter) {
            if (predicate(e)) send(e)
        }
    }

/**
 * Returns a channel containing only elements matching the given [predicate].
 * @param [predicate] function that takes the index of an element and the element itself
 * and returns the result of predicate evaluation on the element.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
// todo: mark predicate with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public fun <E> ReceiveChannel<E>.filterIndexed(context: CoroutineContext = Unconfined, predicate: suspend (index: Int, E) -> Boolean): ReceiveChannel<E> =
    produce(context, onCompletion = consumes()) {
        var index = 0
        for (e in this@filterIndexed) {
            if (predicate(index++, e)) send(e)
        }
    }

/**
 * Appends all elements matching the given [predicate] to the given [destination].
 * @param [predicate] function that takes the index of an element and the element itself
 * and returns the result of predicate evaluation on the element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, C : MutableCollection<in E>> ReceiveChannel<E>.filterIndexedTo(destination: C, predicate: (index: Int, E) -> Boolean): C {
    consumeEachIndexed { (index, element) ->
        if (predicate(index, element)) destination.add(element)
    }
    return destination
}

/**
 * Appends all elements matching the given [predicate] to the given [destination].
 * @param [predicate] function that takes the index of an element and the element itself
 * and returns the result of predicate evaluation on the element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, C : SendChannel<E>> ReceiveChannel<E>.filterIndexedTo(destination: C, predicate: (index: Int, E) -> Boolean): C {
    consumeEachIndexed { (index, element) ->
        if (predicate(index, element)) destination.send(element)
    }
    return destination
}

/**
 * Returns a channel containing all elements not matching the given [predicate].
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
// todo: mark predicate with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public fun <E> ReceiveChannel<E>.filterNot(context: CoroutineContext = Unconfined, predicate: suspend (E) -> Boolean): ReceiveChannel<E> =
    filter(context) { !predicate(it) }

/**
 * @suppress **Deprecated**: For binary compatibility only
 */
@Deprecated("For binary compatibility only", level = DeprecationLevel.HIDDEN)
public fun <E> ReceiveChannel<E>.filterNot(predicate: suspend (E) -> Boolean): ReceiveChannel<E> = filterNot(predicate = predicate)

/**
 * Returns a channel containing all elements that are not `null`.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
@Suppress("UNCHECKED_CAST")
public fun <E : Any> ReceiveChannel<E?>.filterNotNull(): ReceiveChannel<E> =
    filter { it != null } as ReceiveChannel<E>

/**
 * Appends all elements that are not `null` to the given [destination].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E : Any, C : MutableCollection<in E>> ReceiveChannel<E?>.filterNotNullTo(destination: C): C {
    consumeEach {
        if (it != null) destination.add(it)
    }
    return destination
}

/**
 * Appends all elements that are not `null` to the given [destination].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E : Any, C : SendChannel<E>> ReceiveChannel<E?>.filterNotNullTo(destination: C): C {
    consumeEach {
        if (it != null) destination.send(it)
    }
    return destination
}

/**
 * Appends all elements not matching the given [predicate] to the given [destination].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, C : MutableCollection<in E>> ReceiveChannel<E>.filterNotTo(destination: C, predicate: (E) -> Boolean): C {
    consumeEach {
        if (!predicate(it)) destination.add(it)
    }
    return destination
}

/**
 * Appends all elements not matching the given [predicate] to the given [destination].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, C : SendChannel<E>> ReceiveChannel<E>.filterNotTo(destination: C, predicate: (E) -> Boolean): C {
    consumeEach {
        if (!predicate(it)) destination.send(it)
    }
    return destination
}

/**
 * Appends all elements matching the given [predicate] to the given [destination].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, C : MutableCollection<in E>> ReceiveChannel<E>.filterTo(destination: C, predicate: (E) -> Boolean): C {
    consumeEach {
        if (predicate(it)) destination.add(it)
    }
    return destination
}

/**
 * Appends all elements matching the given [predicate] to the given [destination].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, C : SendChannel<E>> ReceiveChannel<E>.filterTo(destination: C, predicate: (E) -> Boolean): C {
    consumeEach {
        if (predicate(it)) destination.send(it)
    }
    return destination
}

/**
 * Returns a channel containing first [n] elements.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public fun <E> ReceiveChannel<E>.take(n: Int, context: CoroutineContext = Unconfined): ReceiveChannel<E> =
    produce(context, onCompletion = consumes()) {
        if (n == 0) return@produce
        require(n >= 0) { "Requested element count $n is less than zero." }
        var remaining: Int = n
        for (e in this@take) {
            send(e)
            remaining--
            if (remaining == 0)
                return@produce
        }
    }

/**
 * Returns a channel containing first elements satisfying the given [predicate].
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
// todo: mark predicate with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public fun <E> ReceiveChannel<E>.takeWhile(context: CoroutineContext = Unconfined, predicate: suspend (E) -> Boolean): ReceiveChannel<E> =
    produce(context, onCompletion = consumes()) {
        for (e in this@takeWhile) {
            if (!predicate(e)) return@produce
            send(e)
        }
    }

/**
 * Returns a [Map] containing key-value pairs provided by [transform] function
 * applied to elements of the given channel.
 *
 * If any of two pairs would have the same key the last one gets added to the map.
 *
 * The returned map preserves the entry iteration order of the original channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, K, V> ReceiveChannel<E>.associate(transform: (E) -> Pair<K, V>): Map<K, V> =
    associateTo(LinkedHashMap(), transform)

/**
 * Returns a [Map] containing the elements from the given channel indexed by the key
 * returned from [keySelector] function applied to each element.
 *
 * If any two elements would have the same key returned by [keySelector] the last one gets added to the map.
 *
 * The returned map preserves the entry iteration order of the original channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, K> ReceiveChannel<E>.associateBy(keySelector: (E) -> K): Map<K, E> =
    associateByTo(LinkedHashMap(), keySelector)

/**
 * Returns a [Map] containing the values provided by [valueTransform] and indexed by [keySelector] functions applied to elements of the given channel.
 *
 * If any two elements would have the same key returned by [keySelector] the last one gets added to the map.
 *
 * The returned map preserves the entry iteration order of the original channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, K, V> ReceiveChannel<E>.associateBy(keySelector: (E) -> K, valueTransform: (E) -> V): Map<K, V> =
    associateByTo(LinkedHashMap(), keySelector, valueTransform)

/**
 * Populates and returns the [destination] mutable map with key-value pairs,
 * where key is provided by the [keySelector] function applied to each element of the given channel
 * and value is the element itself.
 *
 * If any two elements would have the same key returned by [keySelector] the last one gets added to the map.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, K, M : MutableMap<in K, in E>> ReceiveChannel<E>.associateByTo(destination: M, keySelector: (E) -> K): M {
    consumeEach {
        destination.put(keySelector(it), it)
    }
    return destination
}

/**
 * Populates and returns the [destination] mutable map with key-value pairs,
 * where key is provided by the [keySelector] function and
 * and value is provided by the [valueTransform] function applied to elements of the given channel.
 *
 * If any two elements would have the same key returned by [keySelector] the last one gets added to the map.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, K, V, M : MutableMap<in K, in V>> ReceiveChannel<E>.associateByTo(destination: M, keySelector: (E) -> K, valueTransform: (E) -> V): M {
    consumeEach {
        destination.put(keySelector(it), valueTransform(it))
    }
    return destination
}

/**
 * Populates and returns the [destination] mutable map with key-value pairs
 * provided by [transform] function applied to each element of the given channel.
 *
 * If any of two pairs would have the same key the last one gets added to the map.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, K, V, M : MutableMap<in K, in V>> ReceiveChannel<E>.associateTo(destination: M, transform: (E) -> Pair<K, V>): M {
    consumeEach {
        destination += transform(it)
    }
    return destination
}

/**
 * Send each element of the original channel
 * and appends the results to the given [destination].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E, C : SendChannel<E>> ReceiveChannel<E>.toChannel(destination: C): C {
    consumeEach {
        destination.send(it)
    }
    return destination
}

/**
 * Appends all elements to the given [destination] collection.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E, C : MutableCollection<in E>> ReceiveChannel<E>.toCollection(destination: C): C {
    consumeEach {
        destination.add(it)
    }
    return destination
}

/**
 * Returns a [List] containing all elements.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.toList(): List<E> =
    this.toMutableList()

/**
 * Returns a [Map] filled with all elements of this channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <K, V> ReceiveChannel<Pair<K, V>>.toMap(): Map<K, V> =
    toMap(LinkedHashMap())

/**
 * Returns a [MutableMap] filled with all elements of this channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <K, V, M : MutableMap<in K, in V>> ReceiveChannel<Pair<K, V>>.toMap(destination: M): M {
    consumeEach {
        destination += it
    }
    return destination
}

/**
 * Returns a [MutableList] filled with all elements of this channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.toMutableList(): MutableList<E> =
    toCollection(ArrayList())

/**
 * Returns a [Set] of all elements.
 *
 * The returned set preserves the element iteration order of the original channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.toSet(): Set<E> =
    this.toMutableSet()

/**
 * Returns a single channel of all elements from results of [transform] function being invoked on each element of original channel.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
// todo: mark predicate with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public fun <E, R> ReceiveChannel<E>.flatMap(context: CoroutineContext = Unconfined, transform: suspend (E) -> ReceiveChannel<R>): ReceiveChannel<R> =
    produce(context, onCompletion = consumes()) {
        for (e in this@flatMap) {
            transform(e).toChannel(this)
        }
    }

/**
 * Groups elements of the original channel by the key returned by the given [keySelector] function
 * applied to each element and returns a map where each group key is associated with a list of corresponding elements.
 *
 * The returned map preserves the entry iteration order of the keys produced from the original channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, K> ReceiveChannel<E>.groupBy(keySelector: (E) -> K): Map<K, List<E>> =
    groupByTo(LinkedHashMap(), keySelector)

/**
 * Groups values returned by the [valueTransform] function applied to each element of the original channel
 * by the key returned by the given [keySelector] function applied to the element
 * and returns a map where each group key is associated with a list of corresponding values.
 *
 * The returned map preserves the entry iteration order of the keys produced from the original channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, K, V> ReceiveChannel<E>.groupBy(keySelector: (E) -> K, valueTransform: (E) -> V): Map<K, List<V>> =
    groupByTo(LinkedHashMap(), keySelector, valueTransform)

/**
 * Groups elements of the original channel by the key returned by the given [keySelector] function
 * applied to each element and puts to the [destination] map each group key associated with a list of corresponding elements.
 *
 * @return The [destination] map.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, K, M : MutableMap<in K, MutableList<E>>> ReceiveChannel<E>.groupByTo(destination: M, keySelector: (E) -> K): M {
    consumeEach {
        val key = keySelector(it)
        val list = destination.getOrPut(key) { ArrayList() }
        list.add(it)
    }
    return destination
}

/**
 * Groups values returned by the [valueTransform] function applied to each element of the original channel
 * by the key returned by the given [keySelector] function applied to the element
 * and puts to the [destination] map each group key associated with a list of corresponding values.
 *
 * @return The [destination] map.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, K, V, M : MutableMap<in K, MutableList<V>>> ReceiveChannel<E>.groupByTo(destination: M, keySelector: (E) -> K, valueTransform: (E) -> V): M {
    consumeEach {
        val key = keySelector(it)
        val list = destination.getOrPut(key) { ArrayList() }
        list.add(valueTransform(it))
    }
    return destination
}

/**
 * Returns a channel containing the results of applying the given [transform] function
 * to each element in the original channel.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
// todo: mark transform with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public fun <E, R> ReceiveChannel<E>.map(context: CoroutineContext = Unconfined, transform: suspend (E) -> R): ReceiveChannel<R> =
    produce(context, onCompletion = consumes()) {
        consumeEach {
            send(transform(it))
        }
    }

/**
 * Returns a channel containing the results of applying the given [transform] function
 * to each element and its index in the original channel.
 * @param [transform] function that takes the index of an element and the element itself
 * and returns the result of the transform applied to the element.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
// todo: mark predicate with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public fun <E, R> ReceiveChannel<E>.mapIndexed(context: CoroutineContext = Unconfined, transform: suspend (index: Int, E) -> R): ReceiveChannel<R> =
    produce(context, onCompletion = consumes()) {
        var index = 0
        for (e in this@mapIndexed) {
            send(transform(index++, e))
        }
    }

/**
 * Returns a channel containing only the non-null results of applying the given [transform] function
 * to each element and its index in the original channel.
 * @param [transform] function that takes the index of an element and the element itself
 * and returns the result of the transform applied to the element.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
// todo: mark predicate with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public fun <E, R : Any> ReceiveChannel<E>.mapIndexedNotNull(context: CoroutineContext = Unconfined, transform: suspend (index: Int, E) -> R?): ReceiveChannel<R> =
    mapIndexed(context, transform).filterNotNull()

/**
 * Applies the given [transform] function to each element and its index in the original channel
 * and appends only the non-null results to the given [destination].
 * @param [transform] function that takes the index of an element and the element itself
 * and returns the result of the transform applied to the element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, R : Any, C : MutableCollection<in R>> ReceiveChannel<E>.mapIndexedNotNullTo(destination: C, transform: (index: Int, E) -> R?): C {
    consumeEachIndexed { (index, element) ->
        transform(index, element)?.let { destination.add(it) }
    }
    return destination
}

/**
 * Applies the given [transform] function to each element and its index in the original channel
 * and appends only the non-null results to the given [destination].
 * @param [transform] function that takes the index of an element and the element itself
 * and returns the result of the transform applied to the element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, R : Any, C : SendChannel<R>> ReceiveChannel<E>.mapIndexedNotNullTo(destination: C, transform: (index: Int, E) -> R?): C {
    consumeEachIndexed { (index, element) ->
        transform(index, element)?.let { destination.send(it) }
    }
    return destination
}

/**
 * Applies the given [transform] function to each element and its index in the original channel
 * and appends the results to the given [destination].
 * @param [transform] function that takes the index of an element and the element itself
 * and returns the result of the transform applied to the element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, R, C : MutableCollection<in R>> ReceiveChannel<E>.mapIndexedTo(destination: C, transform: (index: Int, E) -> R): C {
    var index = 0
    consumeEach {
        destination.add(transform(index++, it))
    }
    return destination
}

/**
 * Applies the given [transform] function to each element and its index in the original channel
 * and appends the results to the given [destination].
 * @param [transform] function that takes the index of an element and the element itself
 * and returns the result of the transform applied to the element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, R, C : SendChannel<R>> ReceiveChannel<E>.mapIndexedTo(destination: C, transform: (index: Int, E) -> R): C {
    var index = 0
    consumeEach {
        destination.send(transform(index++, it))
    }
    return destination
}

/**
 * Returns a channel containing only the non-null results of applying the given [transform] function
 * to each element in the original channel.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
// todo: mark predicate with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public fun <E, R : Any> ReceiveChannel<E>.mapNotNull(context: CoroutineContext = Unconfined, transform: suspend (E) -> R?): ReceiveChannel<R> =
    map(context, transform).filterNotNull()

/**
 * Applies the given [transform] function to each element in the original channel
 * and appends only the non-null results to the given [destination].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, R : Any, C : MutableCollection<in R>> ReceiveChannel<E>.mapNotNullTo(destination: C, transform: (E) -> R?): C {
    consumeEach {
        transform(it)?.let { destination.add(it) }
    }
    return destination
}

/**
 * Applies the given [transform] function to each element in the original channel
 * and appends only the non-null results to the given [destination].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, R : Any, C : SendChannel<R>> ReceiveChannel<E>.mapNotNullTo(destination: C, transform: (E) -> R?): C {
    consumeEach {
        transform(it)?.let { destination.send(it) }
    }
    return destination
}

/**
 * Applies the given [transform] function to each element of the original channel
 * and appends the results to the given [destination].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, R, C : MutableCollection<in R>> ReceiveChannel<E>.mapTo(destination: C, transform: (E) -> R): C {
    consumeEach {
        destination.add(transform(it))
    }
    return destination
}

/**
 * Applies the given [transform] function to each element of the original channel
 * and appends the results to the given [destination].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, R, C : SendChannel<R>> ReceiveChannel<E>.mapTo(destination: C, transform: (E) -> R): C {
    consumeEach {
        destination.send(transform(it))
    }
    return destination
}

/**
 * Returns a channel of [IndexedValue] for each element of the original channel.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public fun <E> ReceiveChannel<E>.withIndex(context: CoroutineContext = Unconfined): ReceiveChannel<IndexedValue<E>> =
    produce(context, onCompletion = consumes()) {
        var index = 0
        for (e in this@withIndex) {
            send(IndexedValue(index++, e))
        }
    }

/**
 * Returns a channel containing only distinct elements from the given channel.
 *
 * The elements in the resulting channel are in the same order as they were in the source channel.
 *
 * The operation is _intermediate_ and _stateful_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public fun <E> ReceiveChannel<E>.distinct(): ReceiveChannel<E> =
    this.distinctBy { it }

/**
 * Returns a channel containing only elements from the given channel
 * having distinct keys returned by the given [selector] function.
 *
 * The elements in the resulting channel are in the same order as they were in the source channel.
 *
 * The operation is _intermediate_ and _stateful_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
// todo: mark predicate with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public fun <E, K> ReceiveChannel<E>.distinctBy(context: CoroutineContext = Unconfined, selector: suspend (E) -> K): ReceiveChannel<E> =
    produce(context, onCompletion = consumes()) {
        val keys = HashSet<K>()
        for (e in this@distinctBy) {
            val k = selector(e)
            if (k !in keys) {
                send(e)
                keys += k
            }
        }
    }

/**
 * Returns a mutable set containing all distinct elements from the given channel.
 *
 * The returned set preserves the element iteration order of the original channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.toMutableSet(): MutableSet<E> =
    toCollection(LinkedHashSet())

/**
 * Returns `true` if all elements match the given [predicate].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.all(predicate: (E) -> Boolean): Boolean {
    consumeEach {
        if (!predicate(it)) return false
    }
    return true
}

/**
 * Returns `true` if channel has at least one element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.any(): Boolean =
    consume {
        return iterator().hasNext()
    }

/**
 * Returns `true` if at least one element matches the given [predicate].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.any(predicate: (E) -> Boolean): Boolean {
    consumeEach {
        if (predicate(it)) return true
    }
    return false
}

/**
 * Returns the number of elements in this channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.count(): Int {
    var count = 0
    consumeEach { count++ }
    return count
}

/**
 * Returns the number of elements matching the given [predicate].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.count(predicate: (E) -> Boolean): Int {
    var count = 0
    consumeEach {
        if (predicate(it)) count++
    }
    return count
}

/**
 * Accumulates value starting with [initial] value and applying [operation] from left to right to current accumulator value and each element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, R> ReceiveChannel<E>.fold(initial: R, operation: (acc: R, E) -> R): R {
    var accumulator = initial
    consumeEach {
        accumulator = operation(accumulator, it)
    }
    return accumulator
}

/**
 * Accumulates value starting with [initial] value and applying [operation] from left to right
 * to current accumulator value and each element with its index in the original channel.
 * @param [operation] function that takes the index of an element, current accumulator value
 * and the element itself, and calculates the next accumulator value.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, R> ReceiveChannel<E>.foldIndexed(initial: R, operation: (index: Int, acc: R, E) -> R): R {
    var index = 0
    var accumulator = initial
    consumeEach {
        accumulator = operation(index++, accumulator, it)
    }
    return accumulator
}

/**
 * Returns the first element yielding the largest value of the given function or `null` if there are no elements.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, R : Comparable<R>> ReceiveChannel<E>.maxBy(selector: (E) -> R): E? =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext()) return null
        var maxElem = iterator.next()
        var maxValue = selector(maxElem)
        while (iterator.hasNext()) {
            val e = iterator.next()
            val v = selector(e)
            if (maxValue < v) {
                maxElem = e
                maxValue = v
            }
        }
        return maxElem
    }

/**
 * Returns the first element having the largest value according to the provided [comparator] or `null` if there are no elements.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.maxWith(comparator: Comparator<in E>): E? =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext()) return null
        var max = iterator.next()
        while (iterator.hasNext()) {
            val e = iterator.next()
            if (comparator.compare(max, e) < 0) max = e
        }
        return max
    }

/**
 * Returns the first element yielding the smallest value of the given function or `null` if there are no elements.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E, R : Comparable<R>> ReceiveChannel<E>.minBy(selector: (E) -> R): E? =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext()) return null
        var minElem = iterator.next()
        var minValue = selector(minElem)
        while (iterator.hasNext()) {
            val e = iterator.next()
            val v = selector(e)
            if (minValue > v) {
                minElem = e
                minValue = v
            }
        }
        return minElem
    }

/**
 * Returns the first element having the smallest value according to the provided [comparator] or `null` if there are no elements.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.minWith(comparator: Comparator<in E>): E? =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext()) return null
        var min = iterator.next()
        while (iterator.hasNext()) {
            val e = iterator.next()
            if (comparator.compare(min, e) > 0) min = e
        }
        return min
    }

/**
 * Returns `true` if the channel has no elements.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend fun <E> ReceiveChannel<E>.none(): Boolean =
    consume {
        return !iterator().hasNext()
    }

/**
 * Returns `true` if no elements match the given [predicate].
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.none(predicate: (E) -> Boolean): Boolean {
    consumeEach {
        if (predicate(it)) return false
    }
    return true
}

/**
 * Accumulates value starting with the first element and applying [operation] from left to right to current accumulator value and each element.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <S, E : S> ReceiveChannel<E>.reduce(operation: (acc: S, E) -> S): S =
    consume {
        val iterator = this.iterator()
        if (!iterator.hasNext()) throw UnsupportedOperationException("Empty channel can't be reduced.")
        var accumulator: S = iterator.next()
        while (iterator.hasNext()) {
            accumulator = operation(accumulator, iterator.next())
        }
        return accumulator
    }

/**
 * Accumulates value starting with the first element and applying [operation] from left to right
 * to current accumulator value and each element with its index in the original channel.
 * @param [operation] function that takes the index of an element, current accumulator value
 * and the element itself and calculates the next accumulator value.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
// todo: mark operation with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public suspend inline fun <S, E : S> ReceiveChannel<E>.reduceIndexed(operation: (index: Int, acc: S, E) -> S): S =
    consume {
        val iterator = this.iterator()
        if (!iterator.hasNext()) throw UnsupportedOperationException("Empty channel can't be reduced.")
        var index = 1
        var accumulator: S = iterator.next()
        while (iterator.hasNext()) {
            accumulator = operation(index++, accumulator, iterator.next())
        }
        return accumulator
    }

/**
 * Returns the sum of all values produced by [selector] function applied to each element in the channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.sumBy(selector: (E) -> Int): Int {
    var sum = 0
    consumeEach {
        sum += selector(it)
    }
    return sum
}

/**
 * Returns the sum of all values produced by [selector] function applied to each element in the channel.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.sumByDouble(selector: (E) -> Double): Double {
    var sum = 0.0
    consumeEach {
        sum += selector(it)
    }
    return sum
}

/**
 * Returns an original collection containing all the non-`null` elements, throwing an [IllegalArgumentException] if there are any `null` elements.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public fun <E : Any> ReceiveChannel<E?>.requireNoNulls(): ReceiveChannel<E> =
    map { it ?: throw IllegalArgumentException("null element found in $this.") }

/**
 * Splits the original channel into pair of lists,
 * where *first* list contains elements for which [predicate] yielded `true`,
 * while *second* list contains elements for which [predicate] yielded `false`.
 *
 * The operation is _terminal_.
 * This function [consumes][ReceiveChannel.consume] all elements of the original [ReceiveChannel].
 */
public suspend inline fun <E> ReceiveChannel<E>.partition(predicate: (E) -> Boolean): Pair<List<E>, List<E>> {
    val first = ArrayList<E>()
    val second = ArrayList<E>()
    consumeEach {
        if (predicate(it)) {
            first.add(it)
        } else {
            second.add(it)
        }
    }
    return Pair(first, second)
}

/**
 * Returns a channel of pairs built from elements of both channels with same indexes.
 * Resulting channel has length of shortest input channel.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][ReceiveChannel.consume] all elements of both the original [ReceiveChannel] and the `other` one.
 */
public infix fun <E, R> ReceiveChannel<E>.zip(other: ReceiveChannel<R>): ReceiveChannel<Pair<E, R>> =
    zip(other) { t1, t2 -> t1 to t2 }

/**
 * Returns a channel of values built from elements of both collections with same indexes using provided [transform]. Resulting channel has length of shortest input channels.
 *
 * The operation is _intermediate_ and _stateless_.
 * This function [consumes][consume] all elements of both the original [ReceiveChannel] and the `other` one.
 */
// todo: mark transform with crossinline modifier when it is supported: https://youtrack.jetbrains.com/issue/KT-19159
public fun <E, R, V> ReceiveChannel<E>.zip(other: ReceiveChannel<R>, context: CoroutineContext = Unconfined, transform: (a: E, b: R) -> V): ReceiveChannel<V> =
    produce(context, onCompletion = consumesAll(this, other)) {
        val otherIterator = other.iterator()
        this@zip.consumeEach { element1 ->
            if (!otherIterator.hasNext()) return@consumeEach
            val element2 = otherIterator.next()
            send(transform(element1, element2))
        }
    }


