/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.flow.internal.*
import kotlin.jvm.*
import kotlinx.coroutines.flow.internal.unsafeFlow as flow

/**
 * Returns flow where all subsequent repetitions of the same value are filtered out.
 *
 * Note that any instance of [StateFlow] already behaves as if `distinctUtilChanged` operator is
 * applied to it, so applying `distinctUntilChanged` to a `StateFlow` has no effect.
 * See [StateFlow] documentation on Operator Fusion.
 */
public fun <T> Flow<T>.distinctUntilChanged(): Flow<T> =
    when (this) {
        is StateFlow<*> -> this
        else -> distinctUntilChangedBy(keySelector = idKeySelector, areEquivalent = Equivalent.ByValue)
    }

/**
 * Returns flow where all subsequent repetitions of the same value are filtered out, when compared
 * with each other via the provided [areEquivalent] function.
 */
public fun <T> Flow<T>.distinctUntilChanged(areEquivalent: ValueEquivalence<T>): Flow<T> =
    @Suppress("UNCHECKED_CAST")
    distinctUntilChangedBy(keySelector = idKeySelector as ((T) -> T), areEquivalent = areEquivalent)

/**
 * Returns flow where all subsequent repetitions of the same key are filtered out, where
 * key is extracted with [keySelector] function.
 */
public fun <T, K> Flow<T>.distinctUntilChangedBy(keySelector: (T) -> K): Flow<T> =
    distinctUntilChangedBy(keySelector = keySelector, areEquivalent = Equivalent.ByValue)

/**
 * Returns flow where all subsequent repetitions of the same key are filtered out, where
 * keys are extracted with [keySelector] function and compared with each other via the
 * provided [areEquivalent] function.
 */
private fun <T, K> Flow<T>.distinctUntilChangedBy(
    keySelector: (T) -> K,
    areEquivalent: (old: K, new: K) -> Boolean
): Flow<T> =
    flow {
        var previousKey: Any? = NULL
        collect { value ->
            val key = keySelector(value)
            @Suppress("UNCHECKED_CAST")
            if (previousKey === NULL || !areEquivalent(previousKey as K, key)) {
                previousKey = key
                emit(value)
            }
        }
    }

private val idKeySelector: (Any?) -> Any? = { it }
