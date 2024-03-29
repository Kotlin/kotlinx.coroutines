@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.flow.internal.*
import kotlin.jvm.*

/**
 * Returns flow where all subsequent repetitions of the same value are filtered out.
 *
 * Note that any instance of [StateFlow] already behaves as if `distinctUntilChanged` operator is
 * applied to it, so applying `distinctUntilChanged` to a `StateFlow` has no effect.
 * See [StateFlow] documentation on Operator Fusion.
 * Also, repeated application of `distinctUntilChanged` operator on any flow has no effect.
 */
public fun <T> Flow<T>.distinctUntilChanged(): Flow<T> =
    when (this) {
        is StateFlow<*> -> this // state flows are always distinct
        else -> distinctUntilChangedBy(keySelector = defaultKeySelector, areEquivalent = defaultAreEquivalent)
    }

/**
 * Returns flow where all subsequent repetitions of the same value are filtered out, when compared
 * with each other via the provided [areEquivalent] function.
 *
 * Note that repeated application of `distinctUntilChanged` operator with the same parameter has no effect.
 */
@Suppress("UNCHECKED_CAST")
public fun <T> Flow<T>.distinctUntilChanged(areEquivalent: (old: T, new: T) -> Boolean): Flow<T> =
    distinctUntilChangedBy(keySelector = defaultKeySelector, areEquivalent = areEquivalent as (Any?, Any?) -> Boolean)

/**
 * Returns flow where all subsequent repetitions of the same key are filtered out, where
 * key is extracted with [keySelector] function.
 *
 * Note that repeated application of `distinctUntilChanged` operator with the same parameter has no effect.
 */
public fun <T, K> Flow<T>.distinctUntilChangedBy(keySelector: (T) -> K): Flow<T> =
    distinctUntilChangedBy(keySelector = keySelector, areEquivalent = defaultAreEquivalent)

private val defaultKeySelector: (Any?) -> Any? = { it }

private val defaultAreEquivalent: (Any?, Any?) -> Boolean = { old, new -> old == new }

/**
 * Returns flow where all subsequent repetitions of the same key are filtered out, where
 * keys are extracted with [keySelector] function and compared with each other via the
 * provided [areEquivalent] function.
 *
 * NOTE: It is non-inline to share a single implementing class.
 */
private fun <T> Flow<T>.distinctUntilChangedBy(
    keySelector: (T) -> Any?,
    areEquivalent: (old: Any?, new: Any?) -> Boolean
): Flow<T> = when {
    this is DistinctFlowImpl<*> && this.keySelector === keySelector && this.areEquivalent === areEquivalent -> this // same
    else -> DistinctFlowImpl(this, keySelector, areEquivalent)
}

private class DistinctFlowImpl<T>(
    private val upstream: Flow<T>,
    @JvmField val keySelector: (T) -> Any?,
    @JvmField val areEquivalent: (old: Any?, new: Any?) -> Boolean
): Flow<T> {
    override suspend fun collect(collector: FlowCollector<T>) {
        var previousKey: Any? = NULL
        upstream.collect { value ->
            val key = keySelector(value)
            @Suppress("UNCHECKED_CAST")
            if (previousKey === NULL || !areEquivalent(previousKey, key)) {
                previousKey = key
                collector.emit(value)
            }
        }
    }
}
