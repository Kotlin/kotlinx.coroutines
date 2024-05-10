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
 * Returns a flow containing the results of applying the given [transform] function to each value of the original flow.
 */
public inline fun <T, R> Flow<T>.map(crossinline transform: suspend (value: T) -> R): Flow<R> = transform { value ->
    return@transform emit(transform(value))
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

/**
 * Splits the given flow into a flow of non-overlapping lists each not exceeding the given [size] but never empty.
 * The last emitted list may have fewer elements than the given size.
 *
 * Example of usage:
 * ```
 * flowOf("a", "b", "c", "d", "e")
 *     .chunked(2) // ["a", "b"], ["c", "d"], ["e"]
 *     .map { it.joinToString(separator = "") }
 *     .collect {
 *         println(it) // Prints "ab", "cd", e"
 *     }
 * ```
 *
 * @throws IllegalArgumentException if [size] is not positive.
 */
@ExperimentalCoroutinesApi
public fun <T> Flow<T>.chunked(size: Int): Flow<List<T>> {
    require(size >= 1) { "Expected positive chunk size, but got $size" }
    return flow {
        var result: ArrayList<T>? = null // Do not preallocate anything
        collect { value ->
            // Allocate if needed
            val acc = result ?: ArrayList<T>(size).also { result = it }
            acc.add(value)
            if (acc.size == size) {
                emit(acc)
                // Cleanup, but don't allocate -- it might've been the case this is the last element
                result = null
            }
        }
        result?.let { emit(it) }
    }
}
