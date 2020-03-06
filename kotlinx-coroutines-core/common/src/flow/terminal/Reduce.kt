/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")
@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.flow.internal.unsafeFlow as flow
import kotlin.jvm.*

/**
 * Accumulates value starting with the first element and applying [operation] to current accumulator value and each element.
 * Throws [NoSuchElementException] if flow was empty.
 */
@ExperimentalCoroutinesApi
public suspend fun <S, T : S> Flow<T>.reduce(operation: suspend (accumulator: S, value: T) -> S): S {
    var accumulator: Any? = NULL

    collect { value ->
        accumulator = if (accumulator !== NULL) {
            @Suppress("UNCHECKED_CAST")
            operation(accumulator as S, value)
        } else {
            value
        }
    }

    if (accumulator === NULL) throw NoSuchElementException("Empty flow can't be reduced")
    @Suppress("UNCHECKED_CAST")
    return accumulator as S
}

/**
 * Accumulates value starting with [initial] value and applying [operation] current accumulator value and each element
 */
@ExperimentalCoroutinesApi
public suspend inline fun <T, R> Flow<T>.fold(
    initial: R,
    crossinline operation: suspend (acc: R, value: T) -> R
): R {
    var accumulator = initial
    collect { value ->
        accumulator = operation(accumulator, value)
    }
    return accumulator
}

/**
 * The terminal operator, that awaits for one and only one value to be published.
 * Throws [NoSuchElementException] for empty flow and [IllegalStateException] for flow
 * that contains more than one element.
 */
public suspend fun <T> Flow<T>.single(): T {
    var result: Any? = NULL
    collect { value ->
        if (result !== NULL) error("Expected only one element")
        result = value
    }

    if (result === NULL) throw NoSuchElementException("Expected at least one element")
    @Suppress("UNCHECKED_CAST")
    return result as T
}

/**
 * The terminal operator, that awaits for one and only one value to be published.
 * Throws [IllegalStateException] for flow that contains more than one element.
 */
public suspend fun <T: Any> Flow<T>.singleOrNull(): T? {
    var result: T? = null
    collect { value ->
        if (result != null) error("Expected only one element")
        result = value
    }

    return result
}

/**
 * The terminal operator that returns the first element emitted by the flow and then cancels flow's collection.
 * Throws [NoSuchElementException] if the flow was empty.
 */
public suspend fun <T> Flow<T>.first(): T {
    var result: Any? = NULL
    try {
        collect { value ->
            result = value
            throw AbortFlowException(NopCollector)
        }
    } catch (e: AbortFlowException) {
        // Do nothing
    }

    if (result === NULL) throw NoSuchElementException("Expected at least one element")
    return result as T
}

/**
 * The terminal operator that returns the first element emitted by the flow matching the given [predicate] and then cancels flow's collection.
 * Throws [NoSuchElementException] if the flow has not contained elements matching the [predicate].
 */
public suspend fun <T> Flow<T>.first(predicate: suspend (T) -> Boolean): T {
    var result: Any? = NULL
    try {
        collect { value ->
            if (predicate(value)) {
                result = value
                throw AbortFlowException(NopCollector)
            }
        }
    } catch (e: AbortFlowException) {
        // Do nothing
    }

    if (result === NULL) throw NoSuchElementException("Expected at least one element matching the predicate $predicate")
    return result as T
}
