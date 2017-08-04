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

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.Unconfined
import kotlinx.coroutines.experimental.runBlocking
import kotlin.coroutines.experimental.CoroutineContext

internal const val DEFAULT_CLOSE_MESSAGE = "Channel was closed"

/**
 * Creates a [ProducerJob] to read all element of the [Iterable].
 */
public fun <E> Iterable<E>.asReceiveChannel(context: CoroutineContext = Unconfined): ReceiveChannel<E> = produce(context) {
    for (element in this@asReceiveChannel)
        send(element)
}

/**
 * Creates an [ActorJob] to insert elements in this [MutableCollection].
 */
public fun <E> MutableCollection<E>.asSendChannel(context: CoroutineContext = Unconfined): SendChannel<E> = actor(context) {
    for (element in channel)
        this@asSendChannel += element
}

/**
 * Creates a [Sequence] instance that wraps the original [ReceiveChannel] returning its entries when being emitted.
 */
public fun <E : Any> ReceiveChannel<E>.asSequence(): Sequence<E> =
        generateSequence {
            runBlocking {
                receiveOrNull()
            }
        }

/**
 * Performs the given [action] for each received element.
 */
public inline suspend fun <E> ReceiveChannel<E>.consumeEach(action: (E) -> Unit) {
    for (element in this) action(element)
}

/**
 * @suppress: **Deprecated**: binary compatibility with old code
 */
@Deprecated("binary compatibility with old code", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.consumeEach(action: suspend (E) -> Unit) =
    consumeEach { action(it) }

/**
 * Subscribes to this [BroadcastChannel] and performs the specified action for each received element.
 */
public inline suspend fun <E> BroadcastChannel<E>.consumeEach(action: (E) -> Unit) {
    openSubscription().use { channel ->
        for (x in channel) action(x)
    }
}

/**
 * @suppress: **Deprecated**: binary compatibility with old code
 */
@Deprecated("binary compatibility with old code", level = DeprecationLevel.HIDDEN)
public suspend fun <E> BroadcastChannel<E>.consumeEach(action: suspend (E) -> Unit) =
    consumeEach { action(it) }

/**
 * Performs the given [action] for each received element.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <E> ReceiveChannel<E>.consumeEachIndexed(action: suspend (IndexedValue<E>) -> Unit) {
    var index = 0
    for (element in this) action(IndexedValue(index++, element))
}

/**
 * Removes at least minElements and at most maxElements from this channel and adds them to the given destination collection.
 */
public suspend fun <T : Any?, E : T> ReceiveChannel<E>.drainTo(destination: MutableCollection<T>,
                                                               minElements: Int = 0,
                                                               maxElements: Int = Integer.MAX_VALUE) {
    require(minElements >= 0) { "minElements cannot be negative" }
    require(maxElements >= minElements) { "maxElements cannot be lesser than minElements" }
    repeat(minElements) {
        destination += receive()
    }
    repeat(maxElements - minElements) {
        destination += poll() ?: return
    }
}

/**
 * Returns an element at the given [index] or throws an [IndexOutOfBoundsException] if the [index] is out of bounds of this channel.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.elementAt(index: Int): T {
    return elementAtOrElse(index) { throw IndexOutOfBoundsException("ReceiveChannel doesn't contain element at index $index.") }
}

/**
 * Returns an element at the given [index] or the result of calling the [defaultValue] function if the [index] is out of bounds of this channel.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.elementAtOrElse(index: Int, defaultValue: suspend (Int) -> T): T {
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
 */
public suspend fun <T> ReceiveChannel<T>.elementAtOrNull(index: Int): T? {
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.find(predicate: suspend (T) -> Boolean): T? {
    return firstOrNull(predicate)
}

/**
 * Returns the last element matching the given [predicate], or `null` if no such element was found.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.findLast(predicate: suspend (T) -> Boolean): T? {
    return lastOrNull(predicate)
}

/**
 * Returns first element.
 * @throws [NoSuchElementException] if the channel is empty.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.first(): T {
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.first(predicate: suspend (T) -> Boolean): T {
    for (element in this) if (predicate(element)) return element
    throw NoSuchElementException("ReceiveChannel contains no element matching the predicate.")
}

/**
 * Returns the first element, or `null` if the channel is empty.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.firstOrNull(): T? {
    val iterator = iterator()
    if (!iterator.hasNext())
        return null
    return iterator.next()
}

/**
 * Returns the first element matching the given [predicate], or `null` if element was not found.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.firstOrNull(predicate: suspend (T) -> Boolean): T? {
    for (element in this) if (predicate(element)) return element
    return null
}

/**
 * Returns first index of [element], or -1 if the channel does not contain element.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.indexOf(element: T): Int {
    var index = 0
    for (item in this) {
        if (element == item)
            return index
        index++
    }
    return -1
}

/**
 * Returns index of the first element matching the given [predicate], or -1 if the channel does not contain such element.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.indexOfFirst(predicate: suspend (T) -> Boolean): Int {
    var index = 0
    for (item in this) {
        if (predicate(item))
            return index
        index++
    }
    return -1
}

/**
 * Returns index of the last element matching the given [predicate], or -1 if the channel does not contain such element.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.indexOfLast(predicate: suspend (T) -> Boolean): Int {
    var lastIndex = -1
    var index = 0
    for (item in this) {
        if (predicate(item))
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
 */
public suspend fun <T> ReceiveChannel<T>.last(): T {
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.last(predicate: suspend (T) -> Boolean): T {
    var last: T? = null
    var found = false
    for (element in this) {
        if (predicate(element)) {
            last = element
            found = true
        }
    }
    if (!found) throw NoSuchElementException("ReceiveChannel contains no element matching the predicate.")
    @Suppress("UNCHECKED_CAST")
    return last as T
}

/**
 * Returns last index of [element], or -1 if the channel does not contain element.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.lastIndexOf(element: T): Int {
    var lastIndex = -1
    var index = 0
    for (item in this) {
        if (element == item)
            lastIndex = index
        index++
    }
    return lastIndex
}

/**
 * Returns the last element, or `null` if the channel is empty.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.lastOrNull(): T? {
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.lastOrNull(predicate: suspend (T) -> Boolean): T? {
    var last: T? = null
    for (element in this) {
        if (predicate(element)) {
            last = element
        }
    }
    return last
}

/**
 * Returns the single element, or throws an exception if the channel is empty or has more than one element.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.single(): T {
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.single(predicate: suspend (T) -> Boolean): T {
    var single: T? = null
    var found = false
    for (element in this) {
        if (predicate(element)) {
            if (found) throw IllegalArgumentException("ReceiveChannel contains more than one matching element.")
            single = element
            found = true
        }
    }
    if (!found) throw NoSuchElementException("ReceiveChannel contains no element matching the predicate.")
    @Suppress("UNCHECKED_CAST")
    return single as T
}

/**
 * Returns single element, or `null` if the channel is empty or has more than one element.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.singleOrNull(): T? {
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.singleOrNull(predicate: suspend (T) -> Boolean): T? {
    var single: T? = null
    var found = false
    for (element in this) {
        if (predicate(element)) {
            if (found) return null
            single = element
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
 */
public suspend fun <T> ReceiveChannel<T>.drop(n: Int): ReceiveChannel<T> = produce(CommonPool) {
    require(n >= 0) { "Requested element count $n is less than zero." }
    var remaining: Int = n
    if (remaining > 0)
        for (element in this@drop) {
            remaining--
            if (remaining == 0)
                break
        }
    for (element in this@drop) {
        send(element)
    }
}

/**
 * Returns a channel containing all elements except first elements that satisfy the given [predicate].
 *
 * The operation is _intermediate_ and _stateless_.
 */
public suspend fun <T> ReceiveChannel<T>.dropWhile(predicate: suspend (T) -> Boolean): ReceiveChannel<T> = produce(Unconfined) {
    for (element in this@dropWhile) {
        if (!predicate(element))
            break
    }
    for (element in this@dropWhile) {
        send(element)
    }
}

/**
 * Returns a channel containing only elements matching the given [predicate].
 *
 * The operation is _intermediate_ and _stateless_.
 */
public suspend fun <T> ReceiveChannel<T>.filter(predicate: suspend (T) -> Boolean): ReceiveChannel<T> = produce(Unconfined) {
    for (element in this@filter) {
        if (predicate(element))
            send(element)
    }
}

/**
 * Returns a channel containing only elements matching the given [predicate].
 * @param [predicate] function that takes the index of an element and the element itself
 * and returns the result of predicate evaluation on the element.
 *
 * The operation is _intermediate_ and _stateless_.
 */
public suspend fun <T> ReceiveChannel<T>.filterIndexed(predicate: suspend (index: Int, T) -> Boolean): ReceiveChannel<T> = produce(Unconfined) {
    var index = 0
    for (element in this@filterIndexed) {
        if (predicate(index++, element))
            send(element)
    }
}

/**
 * Appends all elements matching the given [predicate] to the given [destination].
 * @param [predicate] function that takes the index of an element and the element itself
 * and returns the result of predicate evaluation on the element.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, C : MutableCollection<in T>> ReceiveChannel<T>.filterIndexedTo(destination: C, predicate: suspend (index: Int, T) -> Boolean): C {
    consumeEachIndexed { (index, element) ->
        if (predicate(index, element)) destination.add(element)
    }
    return destination
}

/**
 * Returns a channel containing all elements not matching the given [predicate].
 *
 * The operation is _intermediate_ and _stateless_.
 */
public suspend fun <T> ReceiveChannel<T>.filterNot(predicate: suspend (T) -> Boolean): ReceiveChannel<T> = filter() { !predicate(it) }


/**
 * Returns a channel containing all elements that are not `null`.
 *
 * The operation is _intermediate_ and _stateless_.
 */
@Suppress("UNCHECKED_CAST")
public suspend fun <T : Any> ReceiveChannel<T?>.filterNotNull(): ReceiveChannel<T> = filter { it != null } as ReceiveChannel<T>

/**
 * Appends all elements that are not `null` to the given [destination].
 *
 * The operation is _terminal_.
 */
public suspend fun <C : MutableCollection<in T>, T : Any> ReceiveChannel<T?>.filterNotNullTo(destination: C): C {
    for (element in this) if (element != null) destination.add(element)
    return destination
}

/**
 * Appends all elements not matching the given [predicate] to the given [destination].
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, C : MutableCollection<in T>> ReceiveChannel<T>.filterNotTo(destination: C, predicate: suspend (T) -> Boolean): C {
    for (element in this) if (!predicate(element)) destination.add(element)
    return destination
}

/**
 * Appends all elements matching the given [predicate] to the given [destination].
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, C : MutableCollection<in T>> ReceiveChannel<T>.filterTo(destination: C, predicate: suspend (T) -> Boolean): C {
    for (element in this) if (predicate(element)) destination.add(element)
    return destination
}

/**
 * Returns a channel containing first [n] elements.
 *
 * The operation is _intermediate_ and _stateless_.
 */
public suspend fun <T> ReceiveChannel<T>.take(n: Int): ReceiveChannel<T> = produce(CommonPool) {
    if (n == 0) return@produce
    require(n >= 0) { "Requested element count $n is less than zero." }

    var remaining: Int = n
    for (element in this@take) {
        send(element)
        remaining--
        if (remaining == 0)
            return@produce
    }
}

/**
 * Returns a channel containing first elements satisfying the given [predicate].
 *
 * The operation is _intermediate_ and _stateless_.
 */
public suspend fun <T> ReceiveChannel<T>.takeWhile(predicate: suspend (T) -> Boolean): ReceiveChannel<T> = produce(Unconfined) {
    for (element in this@takeWhile) {
        if (!predicate(element)) return@produce
        send(element)
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, K, V> ReceiveChannel<T>.associate(transform: suspend (T) -> Pair<K, V>): Map<K, V> {
    return associateTo(LinkedHashMap<K, V>(), transform)
}

/**
 * Returns a [Map] containing the elements from the given channel indexed by the key
 * returned from [keySelector] function applied to each element.
 *
 * If any two elements would have the same key returned by [keySelector] the last one gets added to the map.
 *
 * The returned map preserves the entry iteration order of the original channel.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, K> ReceiveChannel<T>.associateBy(keySelector: suspend (T) -> K): Map<K, T> {
    return associateByTo(LinkedHashMap<K, T>(), keySelector)
}

/**
 * Returns a [Map] containing the values provided by [valueTransform] and indexed by [keySelector] functions applied to elements of the given channel.
 *
 * If any two elements would have the same key returned by [keySelector] the last one gets added to the map.
 *
 * The returned map preserves the entry iteration order of the original channel.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, K, V> ReceiveChannel<T>.associateBy(keySelector: suspend (T) -> K, valueTransform: suspend (T) -> V): Map<K, V> {
    return associateByTo(LinkedHashMap<K, V>(), keySelector, valueTransform)
}

/**
 * Populates and returns the [destination] mutable map with key-value pairs,
 * where key is provided by the [keySelector] function applied to each element of the given channel
 * and value is the element itself.
 *
 * If any two elements would have the same key returned by [keySelector] the last one gets added to the map.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, K, M : MutableMap<in K, in T>> ReceiveChannel<T>.associateByTo(destination: M, keySelector: suspend (T) -> K): M {
    for (element in this) {
        destination.put(keySelector(element), element)
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, K, V, M : MutableMap<in K, in V>> ReceiveChannel<T>.associateByTo(destination: M, keySelector: suspend (T) -> K, valueTransform: suspend (T) -> V): M {
    for (element in this) {
        destination.put(keySelector(element), valueTransform(element))
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, K, V, M : MutableMap<in K, in V>> ReceiveChannel<T>.associateTo(destination: M, transform: suspend (T) -> Pair<K, V>): M {
    for (element in this) {
        destination += transform(element)
    }
    return destination
}

/**
 * Appends all elements to the given [destination] collection.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, C : MutableCollection<in T>> ReceiveChannel<T>.toCollection(destination: C): C {
    for (item in this) {
        destination.add(item)
    }
    return destination
}

/**
 * Returns a [List] containing all elements.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.toList(): List<T> {
    return this.toMutableList()
}

/**
 * Returns a [Map] filled with all elements of this channel.
 *
 * The operation is _terminal_.
 */
public suspend fun <K, V> ReceiveChannel<Pair<K, V>>.toMap(): Map<K, V> {
    return toMap(LinkedHashMap<K, V>())
}

/**
 * Returns a [MutableMap] filled with all elements of this channel.
 *
 * The operation is _terminal_.
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
 */
public suspend fun <T> ReceiveChannel<T>.toMutableList(): MutableList<T> {
    return toCollection(ArrayList<T>())
}

/**
 * Returns a [Set] of all elements.
 *
 * The returned set preserves the element iteration order of the original channel.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.toSet(): Set<T> {
    return toCollection(LinkedHashSet<T>())
}

/**
 * Returns a single channel of all elements from results of [transform] function being invoked on each element of original channel.
 *
 * The operation is _intermediate_ and _stateless_.
 */
public suspend fun <T, R> ReceiveChannel<T>.flatMap(transform: suspend (T) -> ReceiveChannel<R>): ReceiveChannel<R> = produce(Unconfined) {
    for (element in this@flatMap) {
        for (sub in transform(element)) {
            send(sub)
        }
    }
}

/**
 * Groups elements of the original channel by the key returned by the given [keySelector] function
 * applied to each element and returns a map where each group key is associated with a list of corresponding elements.
 *
 * The returned map preserves the entry iteration order of the keys produced from the original channel.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, K> ReceiveChannel<T>.groupBy(keySelector: suspend (T) -> K): Map<K, List<T>> {
    return groupByTo(LinkedHashMap<K, MutableList<T>>(), keySelector)
}

/**
 * Groups values returned by the [valueTransform] function applied to each element of the original channel
 * by the key returned by the given [keySelector] function applied to the element
 * and returns a map where each group key is associated with a list of corresponding values.
 *
 * The returned map preserves the entry iteration order of the keys produced from the original channel.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, K, V> ReceiveChannel<T>.groupBy(keySelector: suspend (T) -> K, valueTransform: suspend (T) -> V): Map<K, List<V>> {
    return groupByTo(LinkedHashMap<K, MutableList<V>>(), keySelector, valueTransform)
}

/**
 * Groups elements of the original channel by the key returned by the given [keySelector] function
 * applied to each element and puts to the [destination] map each group key associated with a list of corresponding elements.
 *
 * @return The [destination] map.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, K, M : MutableMap<in K, MutableList<T>>> ReceiveChannel<T>.groupByTo(destination: M, keySelector: suspend (T) -> K): M {
    for (element in this) {
        val key = keySelector(element)
        val list = destination.getOrPut(key) { ArrayList<T>() }
        list.add(element)
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, K, V, M : MutableMap<in K, MutableList<V>>> ReceiveChannel<T>.groupByTo(destination: M, keySelector: suspend (T) -> K, valueTransform: suspend (T) -> V): M {
    for (element in this) {
        val key = keySelector(element)
        val list = destination.getOrPut(key) { ArrayList<V>() }
        list.add(valueTransform(element))
    }
    return destination
}

/**
 * Returns a channel containing the results of applying the given [transform] function
 * to each element in the original channel.
 *
 * The operation is _intermediate_ and _stateless_.
 */
public suspend fun <T, R> ReceiveChannel<T>.map(transform: suspend (T) -> R): ReceiveChannel<R> = produce(Unconfined) {
    for (element in this@map) {
        send(transform(element))

    }
}

/**
 * Returns a channel containing the results of applying the given [transform] function
 * to each element and its index in the original channel.
 * @param [transform] function that takes the index of an element and the element itself
 * and returns the result of the transform applied to the element.
 *
 * The operation is _intermediate_ and _stateless_.
 */
public suspend fun <T, R> ReceiveChannel<T>.mapIndexed(transform: suspend (index: Int, T) -> R): ReceiveChannel<R> = produce(Unconfined) {
    var index = 0
    for (element in this@mapIndexed) {
        send(transform(index++, element))

    }
}

/**
 * Returns a channel containing only the non-null results of applying the given [transform] function
 * to each element and its index in the original channel.
 * @param [transform] function that takes the index of an element and the element itself
 * and returns the result of the transform applied to the element.
 *
 * The operation is _intermediate_ and _stateless_.
 */
public suspend fun <T, R : Any> ReceiveChannel<T>.mapIndexedNotNull(transform: suspend (index: Int, T) -> R?): ReceiveChannel<R> =
        mapIndexed(transform).filterNotNull()

/**
 * Applies the given [transform] function to each element and its index in the original channel
 * and appends only the non-null results to the given [destination].
 * @param [transform] function that takes the index of an element and the element itself
 * and returns the result of the transform applied to the element.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, R : Any, C : SendChannel<in R>> ReceiveChannel<T>.mapIndexedNotNullTo(destination: C, transform: suspend (index: Int, T) -> R?): C {
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, R, C : SendChannel<in R>> ReceiveChannel<T>.mapIndexedTo(destination: C, transform: suspend (index: Int, T) -> R): C {
    var index = 0
    for (item in this)
        destination.send(transform(index++, item))
    return destination
}

/**
 * Returns a channel containing only the non-null results of applying the given [transform] function
 * to each element in the original channel.
 *
 * The operation is _intermediate_ and _stateless_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, R : Any> ReceiveChannel<T>.mapNotNull(transform: suspend (T) -> R?): ReceiveChannel<R> =
        map(transform).filterNotNull()

/**
 * Applies the given [transform] function to each element in the original channel
 * and appends only the non-null results to the given [destination].
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, R : Any, C : SendChannel<in R>> ReceiveChannel<T>.mapNotNullTo(destination: C, transform: suspend (T) -> R?): C {
    consumeEach { element -> transform(element)?.let { destination.send(it) } }
    return destination
}

/**
 * Applies the given [transform] function to each element of the original channel
 * and appends the results to the given [destination].
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, R, C : SendChannel<in R>> ReceiveChannel<T>.mapTo(destination: C, transform: suspend (T) -> R): C {
    for (item in this)
        destination.send(transform(item))
    return destination
}

/**
 * Returns a channel of [IndexedValue] for each element of the original channel.
 *
 * The operation is _intermediate_ and _stateless_.
 */
public suspend fun <T> ReceiveChannel<T>.withIndex(): ReceiveChannel<IndexedValue<T>> = produce(CommonPool) {
    var index = 0
    for (element in this@withIndex) {
        send(IndexedValue(index++, element))
    }
}

/**
 * Returns a channel containing only distinct elements from the given channel.
 *
 * The elements in the resulting channel are in the same order as they were in the source channel.
 *
 * The operation is _intermediate_ and _stateful_.
 */
public suspend fun <T> ReceiveChannel<T>.distinct(): ReceiveChannel<T> {
    return this.distinctBy { it }
}

/**
 * Returns a channel containing only elements from the given channel
 * having distinct keys returned by the given [selector] function.
 *
 * The elements in the resulting channel are in the same order as they were in the source channel.
 *
 * The operation is _intermediate_ and _stateful_.
 */
public suspend fun <T, K> ReceiveChannel<T>.distinctBy(selector: suspend (T) -> K): ReceiveChannel<T> = produce(Unconfined) {
    val keys = HashSet<K>()
    for (element in this@distinctBy) {
        val k = selector(element)
        if (k !in keys) {
            send(element)
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
 */
public suspend fun <T> ReceiveChannel<T>.toMutableSet(): MutableSet<T> {
    val set = LinkedHashSet<T>()
    for (item in this) set.add(item)
    return set
}

/**
 * Returns `true` if all elements match the given [predicate].
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.all(predicate: suspend (T) -> Boolean): Boolean {
    for (element in this) if (!predicate(element)) return false
    return true
}

/**
 * Returns `true` if channel has at least one element.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.any(): Boolean {
    for (element in this) return true
    return false
}

/**
 * Returns `true` if at least one element matches the given [predicate].
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.any(predicate: suspend (T) -> Boolean): Boolean {
    for (element in this) if (predicate(element)) return true
    return false
}

/**
 * Returns the number of elements in this channel.
 *
 * The operation is _terminal_.
 */
public suspend fun <T> ReceiveChannel<T>.count(): Int {
    var count = 0
    for (element in this) count++
    return count
}

/**
 * Returns the number of elements matching the given [predicate].
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.count(predicate: suspend (T) -> Boolean): Int {
    var count = 0
    for (element in this) if (predicate(element)) count++
    return count
}

/**
 * Accumulates value starting with [initial] value and applying [operation] from left to right to current accumulator value and each element.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, R> ReceiveChannel<T>.fold(initial: R, operation: suspend (acc: R, T) -> R): R {
    var accumulator = initial
    for (element in this) accumulator = operation(accumulator, element)
    return accumulator
}

/**
 * Accumulates value starting with [initial] value and applying [operation] from left to right
 * to current accumulator value and each element with its index in the original channel.
 * @param [operation] function that takes the index of an element, current accumulator value
 * and the element itself, and calculates the next accumulator value.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, R> ReceiveChannel<T>.foldIndexed(initial: R, operation: suspend (index: Int, acc: R, T) -> R): R {
    var index = 0
    var accumulator = initial
    for (element in this) accumulator = operation(index++, accumulator, element)
    return accumulator
}

/**
 * Returns the first element yielding the largest value of the given function or `null` if there are no elements.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, R : Comparable<R>> ReceiveChannel<T>.maxBy(selector: suspend (T) -> R): T? {
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
 */
public suspend fun <T> ReceiveChannel<T>.maxWith(comparator: Comparator<in T>): T? {
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
 */
public suspend fun <T, R : Comparable<R>> ReceiveChannel<T>.minBy(selector: suspend (T) -> R): T? {
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
 */
public suspend fun <T> ReceiveChannel<T>.minWith(comparator: Comparator<in T>): T? {
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
 */
public suspend fun <T> ReceiveChannel<T>.none(): Boolean {
    for (element in this) return false
    return true
}

/**
 * Returns `true` if no elements match the given [predicate].
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.none(predicate: suspend (T) -> Boolean): Boolean {
    for (element in this) if (predicate(element)) return false
    return true
}

/**
 * Accumulates value starting with the first element and applying [operation] from left to right to current accumulator value and each element.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <S, T : S> ReceiveChannel<T>.reduce(operation: suspend (acc: S, T) -> S): S {
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <S, T : S> ReceiveChannel<T>.reduceIndexed(operation: suspend (index: Int, acc: S, T) -> S): S {
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
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.sumBy(selector: suspend (T) -> Int): Int {
    var sum: Int = 0
    for (element in this) {
        sum += selector(element)
    }
    return sum
}

/**
 * Returns the sum of all values produced by [selector] function applied to each element in the channel.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.sumByDouble(selector: suspend (T) -> Double): Double {
    var sum: Double = 0.0
    for (element in this) {
        sum += selector(element)
    }
    return sum
}

/**
 * Returns an original collection containing all the non-`null` elements, throwing an [IllegalArgumentException] if there are any `null` elements.
 *
 * The operation is _intermediate_ and _stateless_.
 */
public suspend fun <T : Any> ReceiveChannel<T?>.requireNoNulls(): ReceiveChannel<T> {
    return map { it ?: throw IllegalArgumentException("null element found in $this.") }
}

/**
 * Splits the original channel into pair of lists,
 * where *first* list contains elements for which [predicate] yielded `true`,
 * while *second* list contains elements for which [predicate] yielded `false`.
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ReceiveChannel<T>.partition(predicate: suspend (T) -> Boolean): Pair<List<T>, List<T>> {
    val first = ArrayList<T>()
    val second = ArrayList<T>()
    for (element in this) {
        if (predicate(element)) {
            first.add(element)
        } else {
            second.add(element)
        }
    }
    return Pair(first, second)
}

/**
 * Send each element of the original channel
 * and appends the results to the given [destination].
 *
 * The operation is _terminal_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, C : SendChannel<in T>> ReceiveChannel<T>.sendTo(destination: C): C {
    for (item in this)
        destination.send(item)
    return destination
}

/**
 * Returns a channel of pairs built from elements of both channels with same indexes.
 * Resulting channel has length of shortest input channel.
 *
 * The operation is _intermediate_ and _stateless_.
 */
public infix suspend fun <T, R> ReceiveChannel<T>.zip(other: ReceiveChannel<R>): ReceiveChannel<Pair<T, R>> {
    return zip(other) { t1, t2 -> t1 to t2 }
}

/**
 * Returns a channel of values built from elements of both collections with same indexes using provided [transform]. Resulting channel has length of shortest input channels.
 *
 * The operation is _intermediate_ and _stateless_.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T, R, V> ReceiveChannel<T>.zip(other: ReceiveChannel<R>, transform: suspend (a: T, b: R) -> V): ReceiveChannel<V> = produce(Unconfined) {
    for (element1 in this@zip) {
        val element2 = other.receiveOrNull() ?: break
        send(transform(element1, element2))
    }
}

/**
 * Adds [element] into to this channel, **blocking** the caller while this channel [Channel.isFull],
 * or throws exception if the channel [Channel.isClosedForSend] (see [Channel.close] for details).
 *
 * This is a way to call [Channel.send] method inside a blocking code using [runBlocking],
 * so this function should not be used from coroutine.
 */
public fun <E> SendChannel<E>.sendBlocking(element: E) {
    // fast path
    if (offer(element))
        return
    // slow path
    runBlocking {
        send(element)
    }
}
