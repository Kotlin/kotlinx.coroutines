@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.jvm.*


/**
 * Returns `true` if at least one element matches the given [predicate].
 *
 * This operation is *terminal*.
 *
 * @see Iterable.any
 * @see Sequence.any
 */
@ExperimentalCoroutinesApi
public suspend fun <T> Flow<T>.any(predicate: suspend (T) -> Boolean): Boolean {
    var found = false
    collectWhile {
        predicate(it).also { satisfies ->
            if (satisfies) found = true
        }.let(Boolean::not)
    }
    return found
}

/**
 * Returns `true` if all elements match the given [predicate].
 *
 * This operation is *terminal*.
 *
 * Note that if the flow terminates without emitting any elements, the function returns `true` because there
 * are no elements in it that *do not* match the predicate.
 * See a more detailed explanation of this logic concept in ["Vacuous truth"](https://en.wikipedia.org/wiki/Vacuous_truth) article.
 *
 * @see Iterable.all
 * @see Sequence.all
 */
@ExperimentalCoroutinesApi
public suspend fun <T> Flow<T>.all(predicate: suspend (T) -> Boolean): Boolean {
    var foundCounterExample = false
    collectWhile {
        predicate(it).also { satisfies ->
            if (!satisfies) foundCounterExample = true
        }
    }
    return !foundCounterExample
}

/**
 * Returns `true` if none of the elements match the given [predicate].
 *
 * This operation is *terminal*.
 *
 * @see Iterable.none
 * @see Sequence.none
 */
@ExperimentalCoroutinesApi
public suspend fun <T> Flow<T>.none(predicate: suspend (T) -> Boolean): Boolean = !any(predicate)
