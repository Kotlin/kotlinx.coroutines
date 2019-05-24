/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.jvm.*
import kotlinx.coroutines.flow.unsafeFlow as flow

/**
 * Applies [transform] function to each value of the given flow.
 * [transform] is a generic function that may transform emitted element, skip it or emit it multiple times.
 *
 * This operator is useless by itself, but can be used as a building block of user-specific operators:
 * ```
 * fun Flow<Int>.skipOddAndDuplicateEven(): Flow<Int> = transform { value ->
 *     if (value % 2 == 0) { // Emit only even values, but twice
 *         emit(value)
 *         emit(value)
 *     } // Do nothing if odd
 * }
 * ```
 */
@FlowPreview
public inline fun <T, R> Flow<T>.transform(@BuilderInference crossinline transform: suspend FlowCollector<R>.(value: T) -> Unit): Flow<R> {
    return flow {
        collect { value ->
            // kludge, without it Unit will be returned and TCE won't kick in, KT-28938
            return@collect transform(value)
        }
    }
}

/**
 * Returns a flow containing only values of the original flow that matches the given [predicate].
 */
@FlowPreview
public inline fun <T> Flow<T>.filter(crossinline predicate: suspend (T) -> Boolean): Flow<T> = flow {
    collect { value ->
        if (predicate(value)) return@collect emit(value)
    }
}

/**
 * Returns a flow containing only values of the original flow that do not match the given [predicate].
 */
@FlowPreview
public inline fun <T> Flow<T>.filterNot(crossinline predicate: suspend (T) -> Boolean): Flow<T> = flow {
    collect { value ->
        if (!predicate(value)) return@collect emit(value)
    }
}

/**
 * Returns a flow containing only values that are instances of specified type [R].
 */
@FlowPreview
@Suppress("UNCHECKED_CAST")
public inline fun <reified R> Flow<*>.filterIsInstance(): Flow<R> = filter { it is R } as Flow<R>

/**
 * Returns a flow containing only values of the original flow that are not null.
 */
@FlowPreview
public fun <T: Any> Flow<T?>.filterNotNull(): Flow<T> = flow<T> {
    collect { value -> if (value != null) return@collect  emit(value) }
}

/**
 * Returns a flow containing the results of applying the given [transform] function to each value of the original flow.
 */
@FlowPreview
public inline fun <T, R> Flow<T>.map(crossinline transform: suspend (value: T) -> R): Flow<R> = transform { value ->
   return@transform emit(transform(value))
}

/**
 * Returns a flow that contains only non-null results of applying the given [transform] function to each value of the original flow.
 */
@FlowPreview
public inline fun <T, R: Any> Flow<T>.mapNotNull(crossinline transform: suspend (value: T) -> R?): Flow<R> = transform { value ->
    val transformed = transform(value) ?: return@transform
    return@transform emit(transformed)
}

/**
 * Returns a flow which performs the given [action] on each value of the original flow.
 */
@FlowPreview
public fun <T> Flow<T>.onEach(action: suspend (T) -> Unit): Flow<T> = flow {
    collect { value ->
        action(value)
        emit(value)
    }
}
