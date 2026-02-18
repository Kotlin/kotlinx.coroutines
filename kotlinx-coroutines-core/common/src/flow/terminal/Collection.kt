@file:JvmMultifileClass @file:JvmName("FlowKt")

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
 * Collects `this` [Flow] into a [Map]
 * with the key-value pairs provided by the [transform] function applied to each element.
 *
 * If the same key appears in more than one pair, the last one gets added to the map.
 *
 * The entry iteration order of the resulting [Map] is the order of the elements in the original [Flow].
 *
 * The operation is _terminal_.
 *
 * ```
 * val names = flowOf("Grace Hopper", "Jacob Bernoulli", "Johann Bernoulli")
 *
 * val byLastName = names.associate { it.split(" ").let { (firstName, lastName) -> lastName to firstName } }
 *
 * // Jacob Bernoulli does not occur in the map because only the last pair with the same key gets added
 * println(byLastName) // {Hopper=Grace, Bernoulli=Johann}
 * ```
 */
public suspend inline fun <T, K, V> Flow<T>.associate(crossinline transform: suspend (T) -> Pair<K, V>): Map<K, V> =
    associateTo(LinkedHashMap(), transform)

/**
 * Collects `this` [Flow] into a [Map]
 * with the keys provided by the [keySelector] function applied to each element.
 *
 * If the same key is returned for more than one element by [keySelector], the last one gets added to the map.
 *
 * The entry iteration order of the resulting [Map] is the order of the elements in the original [Flow].
 *
 * The operation is _terminal_.
 *
 * ```
 * data class Person(val firstName: String, val lastName: String) {
 *     override fun toString(): String = "$firstName $lastName"
 * }
 *
 * val scientists = flowOf(Person("Grace", "Hopper"), Person("Jacob", "Bernoulli"), Person("Johann", "Bernoulli"))
 *
 * val byLastName = scientists.associateBy { it.lastName }
 *
 * // Jacob Bernoulli does not occur in the map because only the last pair with the same key gets added
 * println(byLastName) // {Hopper=Grace Hopper, Bernoulli=Johann Bernoulli}
 * ```
 */
public suspend inline fun <T, K> Flow<T>.associateBy(crossinline keySelector: suspend (T) -> K): Map<K, T> =
    associateByTo(LinkedHashMap(), keySelector)

/**
 * Collects `this` [Flow] into a [Map]
 * with the keys and values provided by the [keySelector] and [valueTransform] functions applied to each element.
 *
 * If the same key is returned for more than one element by [keySelector], the last one gets added to the map.
 *
 * The entry iteration order of the resulting [Map] is the order of the elements in the original [Flow].
 *
 * The operation is _terminal_.
 *
 * ```
 * data class Person(val firstName: String, val lastName: String)
 *
 * val scientists = flowOf(Person("Grace", "Hopper"), Person("Jacob", "Bernoulli"), Person("Johann", "Bernoulli"))
 *
 * val byLastName = scientists.associateBy({ it.lastName }, { it.firstName })
 *
 * // Jacob Bernoulli does not occur in the map because only the last pair with the same key gets added
 * println(byLastName) // {Hopper=Grace, Bernoulli=Johann}
 * ```
 */
public suspend inline fun <T, K, V> Flow<T>.associateBy(
    crossinline keySelector: suspend (T) -> K, crossinline valueTransform: suspend (T) -> V
): Map<K, V> = associateByTo(LinkedHashMap(), keySelector, valueTransform)

/**
 * Collects `this` [Flow] into the given [Map]
 * with the keys provided by the [keySelector] function applied to each element.
 *
 * The order in which key-value pairs get inserted into the [destination] is
 * the order of the elements in the original [Flow].
 *
 * The operation is _terminal_.
 *
 * ```
 * data class Person(val firstName: String, val lastName: String) {
 *     override fun toString(): String = "$firstName $lastName"
 * }
 *
 * val scientists = flowOf(Person("Grace", "Hopper"), Person("Jacob", "Bernoulli"), Person("Johann", "Bernoulli"))
 *
 * val byLastName = mutableMapOf<String, Person>()
 * println("byLastName.isEmpty() is ${byLastName.isEmpty()}") // true
 *
 * scientists.associateByTo(byLastName) { it.lastName }
 *
 * println("byLastName.isNotEmpty() is ${byLastName.isNotEmpty()}") // true
 * // Jacob Bernoulli does not occur in the map because only the last pair with the same key gets added
 * println(byLastName) // {Hopper=Grace Hopper, Bernoulli=Johann Bernoulli}
 * ```
 */
public suspend inline fun <T, K, M : MutableMap<in K, in T>> Flow<T>.associateByTo(
    destination: M, crossinline keySelector: suspend (T) -> K
): M {
    collect { element ->
        destination[keySelector(element)] = element
    }
    return destination
}

/**
 * Collects `this` [Flow] into the given [Map]
 * with the keys and values provided by the [keySelector] and [valueTransform] functions applied to each element.
 *
 * The order in which key-value pairs get inserted into the [destination] is
 * the order of the elements in the original [Flow].
 *
 * The operation is _terminal_.
 *
 * ```
 * data class Person(val firstName: String, val lastName: String)
 *
 * val scientists = flowOf(Person("Grace", "Hopper"), Person("Jacob", "Bernoulli"), Person("Johann", "Bernoulli"))
 *
 * val byLastName = mutableMapOf<String, String>()
 * println("byLastName.isEmpty() is ${byLastName.isEmpty()}") // true
 *
 * scientists.associateByTo(byLastName, { it.lastName }, { it.firstName} )
 *
 * println("byLastName.isNotEmpty() is ${byLastName.isNotEmpty()}") // true
 * // Jacob Bernoulli does not occur in the map because only the last pair with the same key gets added
 * println(byLastName) // {Hopper=Grace, Bernoulli=Johann}
 * ```
 */
public suspend inline fun <T, K, V, M : MutableMap<in K, in V>> Flow<T>.associateByTo(
    destination: M, crossinline keySelector: suspend (T) -> K, crossinline valueTransform: suspend (T) -> V
): M {
    collect { element ->
        destination[keySelector(element)] = valueTransform(element)
    }
    return destination
}

/**
 * Collects `this` [Flow] into the given [Map]
 * with the key-value pairs provided by the [transform] function applied to each element.
 *
 * The order in which key-value pairs get inserted into the [destination] is
 * the order of the elements in the original [Flow].
 *
 * The operation is _terminal_.
 *
 * ```
 * data class Person(val firstName: String, val lastName: String)
 *
 * val scientists = flowOf(Person("Grace", "Hopper"), Person("Jacob", "Bernoulli"), Person("Johann", "Bernoulli"))
 *
 * val byLastName = mutableMapOf<String, String>()
 * println("byLastName.isEmpty() is ${byLastName.isEmpty()}") // true
 *
 * scientists.associateTo(byLastName) { it.lastName to it.firstName }
 *
 * println("byLastName.isNotEmpty() is ${byLastName.isNotEmpty()}") // true
 * // Jacob Bernoulli does not occur in the map because only the last pair with the same key gets added
 * println(byLastName) // {Hopper=Grace, Bernoulli=Johann}
 * ```
 */
public suspend inline fun <T, K, V, M : MutableMap<in K, in V>> Flow<T>.associateTo(
    destination: M, crossinline transform: suspend (T) -> Pair<K, V>
): M {
    collect { element ->
        destination += transform(element)
    }
    return destination
}

/**
 * Collects `this` [Flow] into a [Map]
 * with the keys being the [Flow] elements and the corresponding values being obtained from them using [valueSelector].
 *
 * If the same element is emitted more than once, the last value returned by [valueSelector] gets added to the map.
 *
 * The entry iteration order of the resulting [Map] is the order of the elements in the original [Flow].
 *
 * The operation is _terminal_.
 *
 * ```
 * val words = flowOf("a", "abc", "ab", "def", "abcd")
 * val withLength = words.associateWith { it.length }
 * println(withLength.keys) // [a, abc, ab, def, abcd]
 * println(withLength.values) // [1, 3, 2, 3, 4]
 * ```
 */
public suspend inline fun <K, V> Flow<K>.associateWith(crossinline valueSelector: suspend (K) -> V): Map<K, V> =
    associateWithTo(LinkedHashMap(), valueSelector)

/**
 * Collects `this` [Flow] into the given [Map]
 * with the keys being the [Flow] elements and the corresponding values being obtained from them using [valueSelector].
 *
 * The order in which key-value pairs get inserted into the [destination] is
 * the order of the elements in the original [Flow].
 *
 * The operation is _terminal_.
 *
 * ```
 * data class Person(val firstName: String, val lastName: String) {
 *     override fun toString(): String = "$firstName $lastName"
 * }
 *
 * val scientists = flowOf(Person("Grace", "Hopper"), Person("Jacob", "Bernoulli"), Person("Jacob", "Bernoulli"))
 * val withLengthOfNames = mutableMapOf<Person, Int>()
 * println("withLengthOfNames.isEmpty() is ${withLengthOfNames.isEmpty()}") // true
 *
 * scientists.associateWithTo(withLengthOfNames) { it.firstName.length + it.lastName.length }
 *
 * println("withLengthOfNames.isNotEmpty() is ${withLengthOfNames.isNotEmpty()}") // true
 * // Jacob Bernoulli only occurs once in the map because only the last pair with the same key gets added
 * println(withLengthOfNames) // {Grace Hopper=11, Jacob Bernoulli=14}
 * ```
 */
public suspend inline fun <K, V, M : MutableMap<in K, in V>> Flow<K>.associateWithTo(
    destination: M, crossinline valueSelector: suspend (K) -> V
): M {
    collect { element ->
        destination[element] = valueSelector(element)
    }
    return destination
}

/**
 * Groups elements of the original [Flow] by the key returned by the given [keySelector] function
 * applied to each element and returns a map where each group key is associated with the list of corresponding elements.
 *
 * The entry iteration order of the resulting [Map] is the order in which the keys were first encountered when
 * applying [keySelector] to the [Flow] elements.
 *
 * The operation is _terminal_.
 *
 * ```
 * val words = flowOf("a", "abc", "ab", "def", "abcd")
 * val byLength = words.groupBy { it.length }
 *
 * println(byLength.keys) // [1, 3, 2, 4]
 * println(byLength.values) // [[a], [abc, def], [ab], [abcd]]
 *
 * val mutableByLength: MutableMap<Int, MutableList<String>> = words.groupByTo(mutableMapOf()) { it.length }
 * // same content as in byLength map, but the map is mutable
 * println("mutableByLength == byLength is ${mutableByLength == byLength}") // true
 * ```
 */
public suspend inline fun <T, K> Flow<T>.groupBy(crossinline keySelector: suspend (T) -> K): Map<K, List<T>> =
    groupByTo(LinkedHashMap<K, MutableList<T>>(), keySelector)

/**
 * Groups values returned by the [valueTransform] function applied to each element of the original [Flow]
 * by the key returned by the given [keySelector] function applied to the element
 * and returns a map where each group key is associated with the list of corresponding values.
 *
 * The entry iteration order of the resulting [Map] is the order in which the keys were first encountered when
 * applying [keySelector] to the [Flow] elements.
 *
 * The operation is _terminal_.
 *
 * ```
 * val nameToTeam = flowOf("Alice" to "Marketing", "Bob" to "Sales", "Carol" to "Marketing")
 * val namesByTeam = nameToTeam.groupBy({ it.second }, { it.first })
 * println(namesByTeam) // {Marketing=[Alice, Carol], Sales=[Bob]}
 *
 * val mutableNamesByTeam = nameToTeam.groupByTo(HashMap(), { it.second }, { it.first })
 * // same content as in namesByTeam map, but the map is mutable
 * println("mutableNamesByTeam == namesByTeam is ${mutableNamesByTeam == namesByTeam}") // true
 * ```
 */
public suspend inline fun <T, K, V> Flow<T>.groupBy(
    crossinline keySelector: suspend (T) -> K, crossinline valueTransform: suspend (T) -> V
): Map<K, List<V>> = groupByTo(LinkedHashMap<K, MutableList<V>>(), keySelector, valueTransform)

/**
 * Groups elements of the original [Flow] by the key returned by the given [keySelector] function
 * applied to each element and puts each group key associated with the list of corresponding elements into the given
 * [Map].
 *
 * @return The [destination] map.
 *
 * The operation is _terminal_.
 *
 * ```
 * val words = flowOf("a", "abc", "ab", "def", "abcd")
 * val byLength = words.groupBy { it.length }
 *
 * println(byLength.keys) // [1, 3, 2, 4]
 * println(byLength.values) // [[a], [abc, def], [ab], [abcd]]
 *
 * val mutableByLength: MutableMap<Int, MutableList<String>> = words.groupByTo(mutableMapOf()) { it.length }
 * // same content as in byLength map, but the map is mutable
 * println("mutableByLength == byLength is ${mutableByLength == byLength}") // true
 * ```
 */
public suspend inline fun <T, K, M : MutableMap<in K, MutableList<T>>> Flow<T>.groupByTo(
    destination: M, crossinline keySelector: suspend (T) -> K
): M {
    collect { element ->
        val key = keySelector(element)
        val list = destination.getOrPut(key) { ArrayList() }
        list.add(element)
    }
    return destination
}

/**
 * Groups values returned by the [valueTransform] function applied to each element of the original [Flow]
 * by the key returned by the given [keySelector] function applied to the element
 * and puts each group key associated with the list of corresponding values into the given [Map].
 *
 * @return The [destination] map.
 *
 * The operation is _terminal_.
 *
 * ```
 * val nameToTeam = flowOf("Alice" to "Marketing", "Bob" to "Sales", "Carol" to "Marketing")
 * val namesByTeam = nameToTeam.groupByTo({ it.second }, { it.first })
 * println(namesByTeam) // {Marketing=[Alice, Carol], Sales=[Bob]}
 *
 * val mutableNamesByTeam = nameToTeam.groupByTo(HashMap(), { it.second }, { it.first })
 * // same content as in namesByTeam map, but the map is mutable
 * println("mutableNamesByTeam == namesByTeam is ${mutableNamesByTeam == namesByTeam}") // true
 * ```
 */
public suspend inline fun <T, K, V, M : MutableMap<in K, MutableList<V>>> Flow<T>.groupByTo(
    destination: M, crossinline keySelector: suspend (T) -> K, crossinline valueTransform: suspend (T) -> V
): M {
    collect { element ->
        val key = keySelector(element)
        val list = destination.getOrPut(key) { ArrayList() }
        list.add(valueTransform(element))
    }
    return destination
}
