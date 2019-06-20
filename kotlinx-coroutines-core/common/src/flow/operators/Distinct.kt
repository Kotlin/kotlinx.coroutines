/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.internal.*
import kotlin.jvm.*
import kotlinx.coroutines.flow.unsafeFlow as flow

/**
 * Returns flow where all subsequent repetitions of the same value are filtered out.
 */
@ExperimentalCoroutinesApi
public fun <T> Flow<T>.distinctUntilChanged(): Flow<T> = distinctUntilChangedBy { it }

/**
 * Returns flow where all subsequent repetitions of the same value are filtered out, when compared
 * with each other via the provided [areEquivalent] function.
 */
@FlowPreview
public fun <T> Flow<T>.distinctUntilChanged(areEquivalent: (old: T, new: T) -> Boolean): Flow<T> =
    distinctUntilChangedBy(keySelector = { it }, areEquivalent = areEquivalent)

/**
 * Returns flow where all subsequent repetitions of the same key are filtered out, where
 * key is extracted with [keySelector] function.
 */
@FlowPreview
public fun <T, K> Flow<T>.distinctUntilChangedBy(keySelector: (T) -> K): Flow<T> =
    distinctUntilChangedBy(keySelector = keySelector, areEquivalent = { old, new -> old == new })

/**
 * Returns flow where all subsequent repetitions of the same key are filtered out, where
 * keys are extracted with [keySelector] function and compared with each other via the
 * provided [areEquivalent] function.
 */
private inline fun <T, K> Flow<T>.distinctUntilChangedBy(
    crossinline keySelector: (T) -> K,
    crossinline areEquivalent: (old: K, new: K) -> Boolean
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
