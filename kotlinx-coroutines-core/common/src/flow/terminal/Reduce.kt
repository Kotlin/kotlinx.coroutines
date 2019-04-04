/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.flow.unsafeFlow as flow
import kotlin.jvm.*

/**
 * Accumulates value starting with the first element and applying [operation] to current accumulator value and each element.
 * Throws [UnsupportedOperationException] if flow was empty.
 */
@FlowPreview
public suspend fun <S, T : S> Flow<T>.reduce(operation: suspend (accumulator: S, value: T) -> S): S {
    var accumulator: Any? = NullSurrogate

    collect { value ->
        accumulator = if (accumulator !== NullSurrogate) {
            @Suppress("UNCHECKED_CAST")
            operation(accumulator as S, value)
        } else {
            value
        }
    }

    if (accumulator === NullSurrogate) throw UnsupportedOperationException("Empty flow can't be reduced")
    @Suppress("UNCHECKED_CAST")
    return accumulator as S
}

/**
 * Accumulates value starting with [initial] value and applying [operation] current accumulator value and each element
 */
@FlowPreview
public suspend fun <T, R> Flow<T>.fold(
    initial: R,
    operation: suspend (acc: R, value: T) -> R
): R {
    var accumulator = initial
    collect { value ->
        accumulator = operation(accumulator, value)
    }
    return accumulator
}

/**
 * Terminal operator, that awaits for one and only one value to be published.
 * Throws [NoSuchElementException] for empty flow and [IllegalStateException] for flow
 * that contains more than one element.
 */
@FlowPreview
public suspend fun <T> Flow<T>.single(): T {
    var result: Any? = NullSurrogate
    collect { value ->
        if (result !== NullSurrogate) error("Expected only one element")
        result = value
    }

    if (result === NullSurrogate) throw NoSuchElementException("Expected at least one element")
    @Suppress("UNCHECKED_CAST")
    return result as T
}

/**
 * Terminal operator, that awaits for one and only one value to be published.
 * Throws [IllegalStateException] for flow that contains more than one element.
 */
@FlowPreview
public suspend fun <T: Any> Flow<T>.singleOrNull(): T? {
    var result: T? = null
    collect { value ->
        if (result != null) error("Expected only one element")
        result = value
    }

    return result
}
