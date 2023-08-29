/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")
@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.internal.*
import kotlin.jvm.*
import kotlin.reflect.*
import kotlinx.coroutines.flow.internal.unsafeFlow as flow
import kotlinx.coroutines.flow.unsafeTransform as transform

/**
 * Returns a flow containing only values of the original flow that match the given [predicate].
 */
public inline fun <T> Flow<T>.filter(crossinline predicate: suspend (T) -> Boolean): Flow<T> = transform { value ->
    if (predicate(value)) return@transform emit(value)
}

/**
 * Returns a flow containing only values of the original flow that do not match the given [predicate].
 */
public inline fun <T> Flow<T>.filterNot(crossinline predicate: suspend (T) -> Boolean): Flow<T> = transform { value ->
    if (!predicate(value)) return@transform emit(value)
}

/**
 * Returns a flow containing only values that are instances of specified type [R].
 */
@Suppress("UNCHECKED_CAST")
public inline fun <reified R> Flow<*>.filterIsInstance(): Flow<R> = filter { it is R } as Flow<R>

/**
 * Returns a flow containing only values that are instances of the given [klass].
 */
public fun <R : Any> Flow<*>.filterIsInstance(klass: KClass<R>): Flow<R> = filter { klass.isInstance(it) } as Flow<R>

/**
 * Returns a flow containing only values of the original flow that are not null.
 */
public fun <T: Any> Flow<T?>.filterNotNull(): Flow<T> = transform<T?, T> { value ->
    if (value != null) return@transform emit(value)
}

/**
 * Returns a flow containing the results of applying the given [transform] function to each value of the original flow with the help of a state.
 */
public inline fun <T, R> Flow<T>.map(crossinline transform: suspend (value: T) -> R): Flow<R> = transform { value ->
    return@transform emit(transform(value))
}

/**
 * Returns a flow containing the results of applying the given [transform] function to each value of the original flow.
 *
 * @param state the initial state
 * @param onCompletion will be called when completion, return a non-null value for optional completion value.
 * @param transform function applied to each value to get a new result with next state
 * @return a new flow
 */
public fun <S, T, R> Flow<T>.statefulMap(
    state: S,
    onCompletion: suspend (S) -> R?,
    transform: suspend (state: S, value: T) -> Pair<S, R>,
): Flow<R> = StatefulMapImpl(this, state, onCompletion, transform)

/**
 * Returns a flow containing the results of applying the given [transform] function to each value of the original flow.
 *
 * @param state the initial state
 * @param transform function applied to each value to get a new result with next state
 * @return a new flow
 */
public fun <S, T, R> Flow<T>.statefulMap(
    state: S,
    transform: suspend (state: S, value: T) -> Pair<S, R>,
): Flow<R> = statefulMap(state, defaultCompletion as ((S) -> R?), transform)

private val defaultCompletion:(Any) -> Any? = {null}

private class StatefulMapImpl<S, T, R>(
    private val upstream: Flow<T>,
    private val state: S,
    private val onCompletion: suspend (S) -> R? = { null },
    private val transform: suspend (state: S, value: T) -> Pair<S, R>
) : Flow<R> {
    override suspend fun collect(collector: FlowCollector<R>) {
        var currentState: S = state
        try {
            upstream.collect { value ->
                val (newState, result) = transform(currentState, value)
                currentState = newState
                collector.emit(result)
            }
        } catch (cause: Throwable) {
            try {
                onCompletion(currentState)?.let {
                    collector.emit(it)
                }
            } catch (e: Throwable) {
                if (cause !== e) e.addSuppressed(cause)
                throw e
            }
            throw cause
        }
        //Normal completion
        onCompletion(currentState)?.let {
            collector.emit(it)
        }
    }
}

/**
 * Returns a flow that contains only non-null results of applying the given [transform] function to each value of the original flow.
 */
public inline fun <T, R: Any> Flow<T>.mapNotNull(crossinline transform: suspend (value: T) -> R?): Flow<R> = transform { value ->
    val transformed = transform(value) ?: return@transform
    return@transform emit(transformed)
}

/**
 * Returns a flow that wraps each element into [IndexedValue], containing value and its index (starting from zero).
 */
public fun <T> Flow<T>.withIndex(): Flow<IndexedValue<T>> = flow {
    var index = 0
    collect { value ->
        emit(IndexedValue(checkIndexOverflow(index++), value))
    }
}

/**
 * Returns a flow that invokes the given [action] **before** each value of the upstream flow is emitted downstream.
 */
public fun <T> Flow<T>.onEach(action: suspend (T) -> Unit): Flow<T> = transform { value ->
    action(value)
    return@transform emit(value)
}

/**
 * Folds the given flow with [operation], emitting every intermediate result, including [initial] value.
 * Note that initial value should be immutable (or should not be mutated) as it is shared between different collectors.
 * For example:
 * ```
 * flowOf(1, 2, 3).scan(emptyList<Int>()) { acc, value -> acc + value }.toList()
 * ```
 * will produce `[[], [1], [1, 2], [1, 2, 3]]`.
 *
 * This function is an alias to [runningFold] operator.
 */
public fun <T, R> Flow<T>.scan(initial: R, @BuilderInference operation: suspend (accumulator: R, value: T) -> R): Flow<R> = runningFold(initial, operation)

/**
 * Folds the given flow with [operation], emitting every intermediate result, including [initial] value.
 * Note that initial value should be immutable (or should not be mutated) as it is shared between different collectors.
 * For example:
 * ```
 * flowOf(1, 2, 3).runningFold(emptyList<Int>()) { acc, value -> acc + value }.toList()
 * ```
 * will produce `[[], [1], [1, 2], [1, 2, 3]]`.
 */
public fun <T, R> Flow<T>.runningFold(initial: R, @BuilderInference operation: suspend (accumulator: R, value: T) -> R): Flow<R> = flow {
    var accumulator: R = initial
    emit(accumulator)
    collect { value ->
        accumulator = operation(accumulator, value)
        emit(accumulator)
    }
}

/**
 * Reduces the given flow with [operation], emitting every intermediate result, including initial value.
 * The first element is taken as initial value for operation accumulator.
 * This operator has a sibling with initial value -- [scan].
 *
 * For example:
 * ```
 * flowOf(1, 2, 3, 4).runningReduce { acc, value -> acc + value }.toList()
 * ```
 * will produce `[1, 3, 6, 10]`
 */
public fun <T> Flow<T>.runningReduce(operation: suspend (accumulator: T, value: T) -> T): Flow<T> = flow {
    var accumulator: Any? = NULL
    collect { value ->
        accumulator = if (accumulator === NULL) {
            value
        } else {
            operation(accumulator as T, value)
        }
        emit(accumulator as T)
    }
}
