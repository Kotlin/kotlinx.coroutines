@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlin.jvm.*

/**
 * Collects given flow into a [destination]
 */
public suspend fun <T> Flow<T>.toList(destination: MutableList<T> = ArrayList()): List<T> = toCollection(destination)

/**
 * Collects given flow into a [destination]
 */
public suspend fun <T> Flow<T>.toSet(destination: MutableSet<T> = LinkedHashSet()): Set<T> = toCollection(destination)

/**
 * Collects given flow into a [destination]
 */
public suspend fun <T, C : MutableCollection<in T>> Flow<T>.toCollection(destination: C): C {
    collect { value ->
        destination.add(value)
    }
    return destination
}

/**
 * Returns a [Map] containing key-value pairs provided by [transform] function
 * applied to elements of the given sequence.
 *
 * If any of two pairs would have the same key the last one gets added to the map.
 *
 * The returned map preserves the entry iteration order of the original sequence.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, K, V> Flow<T>.associate(transform: (T) -> Pair<K, V>): Map<K, V> =
    associateTo(LinkedHashMap(), transform)

/**
 * Returns a [Map] containing the elements from the given sequence indexed by the key
 * returned from [keySelector] function applied to each element.
 *
 * If any two elements would have the same key returned by [keySelector] the last one gets added to the map.
 *
 * The returned map preserves the entry iteration order of the original sequence.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, K> Flow<T>.associateBy(keySelector: (T) -> K): Map<K, T> =
    associateByTo(LinkedHashMap(), keySelector)

/**
 * Returns a [Map] containing the values provided by [valueTransform] and indexed by [keySelector] functions applied to elements of the given sequence.
 *
 * If any two elements would have the same key returned by [keySelector] the last one gets added to the map.
 *
 * The returned map preserves the entry iteration order of the original sequence.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, K, V> Flow<T>.associateBy(keySelector: (T) -> K, valueTransform: (T) -> V): Map<K, V> =
    associateByTo(LinkedHashMap(), keySelector, valueTransform)

/**
 * Populates and returns the [destination] mutable map with key-value pairs,
 * where key is provided by the [keySelector] function applied to each element of the given sequence
 * and value is the element itself.
 *
 * If any two elements would have the same key returned by [keySelector] the last one gets added to the map.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, K, M : MutableMap<in K, in T>> Flow<T>.associateByTo(destination: M, keySelector: (T) -> K): M {
    collect { element ->
        destination[keySelector(element)] = element
    }
    return destination
}

/**
 * Populates and returns the [destination] mutable map with key-value pairs,
 * where key is provided by the [keySelector] function and
 * and value is provided by the [valueTransform] function applied to elements of the given sequence.
 *
 * If any two elements would have the same key returned by [keySelector] the last one gets added to the map.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, K, V, M : MutableMap<in K, in V>> Flow<T>.associateByTo(destination: M, keySelector: (T) -> K, valueTransform: (T) -> V): M {
    collect { element ->
        destination[keySelector(element)] = valueTransform(element)
    }
    return destination
}

/**
 * Populates and returns the [destination] mutable map with key-value pairs
 * provided by [transform] function applied to each element of the given sequence.
 *
 * If any of two pairs would have the same key the last one gets added to the map.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, K, V, M : MutableMap<in K, in V>> Flow<T>.associateTo(destination: M, transform: (T) -> Pair<K, V>): M {
    collect { element ->
        destination += transform(element)
    }
    return destination
}

/**
 * Returns a [Map] where keys are elements from the given sequence and values are
 * produced by the [valueSelector] function applied to each element.
 *
 * If any two elements are equal, the last one gets added to the map.
 *
 * The returned map preserves the entry iteration order of the original sequence.
 *
 * The operation is _terminal_.
 */
public suspend fun <K, V> Flow<K>.associateWith(valueSelector: (K) -> V): Map<K, V> =
    associateWithTo(LinkedHashMap(), valueSelector)

/**
 * Populates and returns the [destination] mutable map with key-value pairs for each element of the given sequence,
 * where key is the element itself and value is provided by the [valueSelector] function applied to that key.
 *
 * If any two elements are equal, the last one overwrites the former value in the map.
 *
 * The operation is _terminal_.
 */
public suspend fun <K, V, M : MutableMap<in K, in V>> Flow<K>.associateWithTo(destination: M, valueSelector: (K) -> V): M {
    collect { element ->
        destination[element] = valueSelector(element)
    }
    return destination
}

/**
 * Groups elements of the original sequence by the key returned by the given [keySelector] function
 * applied to each element and returns a map where each group key is associated with a list of corresponding elements.
 *
 * The returned map preserves the entry iteration order of the keys produced from the original sequence.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, K> Flow<T>.groupBy(keySelector: (T) -> K): Map<K, List<T>> =
    groupByTo(LinkedHashMap<K, MutableList<T>>(), keySelector)

/**
 * Groups values returned by the [valueTransform] function applied to each element of the original sequence
 * by the key returned by the given [keySelector] function applied to the element
 * and returns a map where each group key is associated with a list of corresponding values.
 *
 * The returned map preserves the entry iteration order of the keys produced from the original sequence.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, K, V> Flow<T>.groupBy(keySelector: (T) -> K, valueTransform: (T) -> V): Map<K, List<V>> =
    groupByTo(LinkedHashMap<K, MutableList<V>>(), keySelector, valueTransform)

/**
 * Groups elements of the original sequence by the key returned by the given [keySelector] function
 * applied to each element and puts to the [destination] map each group key associated with a list of corresponding elements.
 *
 * @return The [destination] map.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, K, M : MutableMap<in K, MutableList<T>>> Flow<T>.groupByTo(destination: M, keySelector: (T) -> K): M {
    collect { element ->
        val key = keySelector(element)
        val list = destination.getOrPut(key) { ArrayList() }
        list.add(element)
    }
    return destination
}

/**
 * Groups values returned by the [valueTransform] function applied to each element of the original sequence
 * by the key returned by the given [keySelector] function applied to the element
 * and puts to the [destination] map each group key associated with a list of corresponding values.
 *
 * @return The [destination] map.
 *
 * The operation is _terminal_.
 */
public suspend fun <T, K, V, M : MutableMap<in K, MutableList<V>>> Flow<T>.groupByTo(destination: M, keySelector: (T) -> K, valueTransform: (T) -> V): M {
    collect { element ->
        val key = keySelector(element)
        val list = destination.getOrPut(key) { ArrayList() }
        list.add(valueTransform(element))
    }
    return destination
}
