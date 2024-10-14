@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.jvm.*


/**
 * A terminal operator that returns `true` and immediately cancels the flow
 * if at least one element matches the given [predicate].
 *
 * If the flow does not emit any elements or no element matches the predicate, the function returns `false`.
 *
 * Equivalent to `!all { !predicate(it) }` (see [Flow.all]) and `!none { predicate(it) }` (see [Flow.none]).
 *
 * Example:
 *
 * ```
 * val myFlow = flow {
 *   repeat(10) {
 *     emit(it)
 *   }
 *   throw RuntimeException("You still didn't find the required number? I gave you ten!")
 * }
 * println(myFlow.any { it > 5 }) // true
 * println(flowOf(1, 2, 3).any { it > 5 }) // false
 * ```
 *
 * @see Iterable.any
 * @see Sequence.any
 */
public suspend fun <T> Flow<T>.any(predicate: suspend (T) -> Boolean): Boolean {
    var found = false
    collectWhile {
        val satisfies = predicate(it)
        if (satisfies) found = true
        !satisfies
    }
    return found
}

/**
 * A terminal operator that returns `true` if all elements match the given [predicate],
 * or returns `false` and cancels the flow as soon as the first element not matching the predicate is encountered.
 *
 * If the flow terminates without emitting any elements, the function returns `true` because there
 * are no elements in it that *do not* match the predicate.
 * See a more detailed explanation of this logic concept in the
 * ["Vacuous truth"](https://en.wikipedia.org/wiki/Vacuous_truth) article.
 *
 * Equivalent to `!any { !predicate(it) }` (see [Flow.any]) and `none { !predicate(it) }` (see [Flow.none]).
 *
 * Example:
 *
 * ```
 * val myFlow = flow {
 *   repeat(10) {
 *     emit(it)
 *   }
 *   throw RuntimeException("You still didn't find the required number? I gave you ten!")
 * }
 * println(myFlow.all { it <= 5 }) // false
 * println(flowOf(1, 2, 3).all { it <= 5 }) // true
 * ```
 *
 * @see Iterable.all
 * @see Sequence.all
 */
public suspend fun <T> Flow<T>.all(predicate: suspend (T) -> Boolean): Boolean {
    var foundCounterExample = false
    collectWhile {
        val satisfies = predicate(it)
        if (!satisfies) foundCounterExample = true
        satisfies
    }
    return !foundCounterExample
}

/**
 * A terminal operator that returns `true` if no elements match the given [predicate],
 * or returns `false` and cancels the flow as soon as the first element matching the predicate is encountered.
 *
 * If the flow terminates without emitting any elements, the function returns `true` because there
 * are no elements in it that match the predicate.
 * See a more detailed explanation of this logic concept in the
 * ["Vacuous truth"](https://en.wikipedia.org/wiki/Vacuous_truth) article.
 *
 * Equivalent to `!any(predicate)` (see [Flow.any]) and `all { !predicate(it) }` (see [Flow.all]).
 *
 * Example:
 * ```
 * val myFlow = flow {
 *   repeat(10) {
 *     emit(it)
 *   }
 *   throw RuntimeException("You still didn't find the required number? I gave you ten!")
 * }
 * println(myFlow.none { it > 5 }) // false
 * println(flowOf(1, 2, 3).none { it > 5 }) // true
 * ```
 *
 * @see Iterable.none
 * @see Sequence.none
 */
public suspend fun <T> Flow<T>.none(predicate: suspend (T) -> Boolean): Boolean = !any(predicate)
