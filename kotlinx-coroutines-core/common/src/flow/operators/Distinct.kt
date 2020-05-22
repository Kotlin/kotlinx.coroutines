/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.flow.internal.*
import kotlin.jvm.*

/**
 * Returns flow where all subsequent repetitions of the same value are filtered out.
 *
 * Note that any instance of [StateFlow] already behaves as if `distinctUtilChanged` operator is
 * applied to it, so applying `distinctUntilChanged` to a `StateFlow` has no effect.
 * See [StateFlow] documentation on Operator Fusion.
 */
public fun <T> Flow<T>.distinctUntilChanged(): Flow<T> =
    when {
        this is DistinctFlow<*> && isDefaultEquivalence -> this // some other internal impls beyond StateFlow are distinct, too
        else -> distinctUntilChangedBy(keySelector = defaultKeySelector, areEquivalent = defaultAreEquivalent)
    }

/**
 * Returns flow where all subsequent repetitions of the same value are filtered out, when compared
 * with each other via the provided [areEquivalent] function.
 */
@Suppress("UNCHECKED_CAST")
public fun <T> Flow<T>.distinctUntilChanged(areEquivalent: (old: T, new: T) -> Boolean): Flow<T> =
    distinctUntilChangedBy(keySelector = defaultKeySelector, areEquivalent = areEquivalent as (Any?, Any?) -> Boolean)

/**
 * Returns flow where all subsequent repetitions of the same key are filtered out, where
 * key is extracted with [keySelector] function.
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
 * NOTE: It is non-inline to share a single implelenting class.
 */
private fun <T> Flow<T>.distinctUntilChangedBy(
    keySelector: (T) -> Any?,
    areEquivalent: (old: Any?, new: Any?) -> Boolean
): Flow<T> =
    unsafeDistinctFlow(keySelector === defaultKeySelector && areEquivalent === defaultAreEquivalent) {
        var previousKey: Any? = NULL
        collect { value ->
            val key = keySelector(value)
            @Suppress("UNCHECKED_CAST")
            if (previousKey === NULL || !areEquivalent(previousKey, key)) {
                previousKey = key
                emit(value)
            }
        }
    }
