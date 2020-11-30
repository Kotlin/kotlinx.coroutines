/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")
@file:Suppress("UNCHECKED_CAST", "NON_APPLICABLE_CALL_FOR_BUILDER_INFERENCE") // KT-32203

package kotlinx.coroutines.flow

import kotlinx.coroutines.flow.internal.*
import kotlin.jvm.*
import kotlinx.coroutines.flow.flow as safeFlow
import kotlinx.coroutines.flow.internal.unsafeFlow as flow

/**
 * Returns a [Flow] whose values are generated with [transform] function by combining
 * the most recently emitted values by each flow.
 *
 * It can be demonstrated with the following example:
 * ```
 * val flow = flowOf(1, 2).onEach { delay(10) }
 * val flow2 = flowOf("a", "b", "c").onEach { delay(15) }
 * flow.combine(flow2) { i, s -> i.toString() + s }.collect {
 *     println(it) // Will print "1a 2a 2b 2c"
 * }
 * ```
 *
 * This function is a shorthand for `flow.combineTransform(flow2) { a, b -> emit(transform(a, b)) }
 */
@JvmName("flowCombine")
public fun <T1, T2, R> Flow<T1>.combine(flow: Flow<T2>, transform: suspend (a: T1, b: T2) -> R): Flow<R> = flow {
    combineInternal(arrayOf(this@combine, flow), nullArrayFactory(), { emit(transform(it[0] as T1, it[1] as T2)) })
}

/**
 * Returns a [Flow] whose values are generated with [transform] function by combining
 * the most recently emitted values by each flow.
 *
 * It can be demonstrated with the following example:
 * ```
 * val flow = flowOf(1, 2).onEach { delay(10) }
 * val flow2 = flowOf("a", "b", "c").onEach { delay(15) }
 * combine(flow, flow2) { i, s -> i.toString() + s }.collect {
 *     println(it) // Will print "1a 2a 2b 2c"
 * }
 * ```
 *
 * This function is a shorthand for `combineTransform(flow, flow2) { a, b -> emit(transform(a, b)) }
 */
public fun <T1, T2, R> combine(flow: Flow<T1>, flow2: Flow<T2>, transform: suspend (a: T1, b: T2) -> R): Flow<R> =
    flow.combine(flow2, transform)

/**
 * Returns a [Flow] whose values are generated by [transform] function that process the most recently emitted values by each flow.
 *
 * The receiver of the [transform] is [FlowCollector] and thus `transform` is a
 * generic function that may transform emitted element, skip it or emit it multiple times.
 *
 * Its usage can be demonstrated with the following example:
 * ```
 * val flow = requestFlow()
 * val flow2 = searchEngineFlow()
 * flow.combineTransform(flow2) { request, searchEngine ->
 *     emit("Downloading in progress")
 *     val result = download(request, searchEngine)
 *     emit(result)
 * }
 * ```
 */
@JvmName("flowCombineTransform")
public fun <T1, T2, R> Flow<T1>.combineTransform(
    flow: Flow<T2>,
    @BuilderInference transform: suspend FlowCollector<R>.(a: T1, b: T2) -> Unit
): Flow<R> = combineTransformUnsafe(this, flow) { args: Array<*> ->
    transform(
        args[0] as T1,
        args[1] as T2
    )
}

/**
 * Returns a [Flow] whose values are generated by [transform] function that process the most recently emitted values by each flow.
 *
 * The receiver of the [transform] is [FlowCollector] and thus `transform` is a
 * generic function that may transform emitted element, skip it or emit it multiple times.
 *
 * Its usage can be demonstrated with the following example:
 * ```
 * val flow = requestFlow()
 * val flow2 = searchEngineFlow()
 * combineTransform(flow, flow2) { request, searchEngine ->
 *     emit("Downloading in progress")
 *     val result = download(request, searchEngine)
 *     emit(result)
 * }
 * ```
 */
public fun <T1, T2, R> combineTransform(
    flow: Flow<T1>,
    flow2: Flow<T2>,
    @BuilderInference transform: suspend FlowCollector<R>.(a: T1, b: T2) -> Unit
): Flow<R> = combineTransformUnsafe(flow, flow2) { args: Array<*> ->
    transform(
        args[0] as T1,
        args[1] as T2
    )
}

/**
 * Returns a [Flow] whose values are generated with [transform] function by combining
 * the most recently emitted values by each flow.
 */
public fun <T1, T2, T3, R> combine(
    flow: Flow<T1>,
    flow2: Flow<T2>,
    flow3: Flow<T3>,
    @BuilderInference transform: suspend (T1, T2, T3) -> R
): Flow<R> = combineUnsafe(flow, flow2, flow3) { args: Array<*> ->
    transform(
        args[0] as T1,
        args[1] as T2,
        args[2] as T3
    )
}

/**
 * Returns a [Flow] whose values are generated by [transform] function that process the most recently emitted values by each flow.
 *
 * The receiver of the [transform] is [FlowCollector] and thus `transform` is a
 * generic function that may transform emitted element, skip it or emit it multiple times.
 */
public fun <T1, T2, T3, R> combineTransform(
    flow: Flow<T1>,
    flow2: Flow<T2>,
    flow3: Flow<T3>,
    @BuilderInference transform: suspend FlowCollector<R>.(T1, T2, T3) -> Unit
): Flow<R> = combineTransformUnsafe(flow, flow2, flow3) { args: Array<*> ->
    transform(
        args[0] as T1,
        args[1] as T2,
        args[2] as T3
    )
}

/**
 * Returns a [Flow] whose values are generated with [transform] function by combining
 * the most recently emitted values by each flow.
 */
public fun <T1, T2, T3, T4, R> combine(
    flow: Flow<T1>,
    flow2: Flow<T2>,
    flow3: Flow<T3>,
    flow4: Flow<T4>,
    transform: suspend (T1, T2, T3, T4) -> R
): Flow<R> = combineUnsafe(flow, flow2, flow3, flow4) { args: Array<*> ->
    transform(
        args[0] as T1,
        args[1] as T2,
        args[2] as T3,
        args[3] as T4
    )
}

/**
 * Returns a [Flow] whose values are generated by [transform] function that process the most recently emitted values by each flow.
 *
 * The receiver of the [transform] is [FlowCollector] and thus `transform` is a
 * generic function that may transform emitted element, skip it or emit it multiple times.
 */
public fun <T1, T2, T3, T4, R> combineTransform(
    flow: Flow<T1>,
    flow2: Flow<T2>,
    flow3: Flow<T3>,
    flow4: Flow<T4>,
    @BuilderInference transform: suspend FlowCollector<R>.(T1, T2, T3, T4) -> Unit
): Flow<R> = combineTransformUnsafe(flow, flow2, flow3, flow4) { args: Array<*> ->
    transform(
        args[0] as T1,
        args[1] as T2,
        args[2] as T3,
        args[3] as T4
    )
}

/**
 * Returns a [Flow] whose values are generated with [transform] function by combining
 * the most recently emitted values by each flow.
 */
public fun <T1, T2, T3, T4, T5, R> combine(
    flow: Flow<T1>,
    flow2: Flow<T2>,
    flow3: Flow<T3>,
    flow4: Flow<T4>,
    flow5: Flow<T5>,
    transform: suspend (T1, T2, T3, T4, T5) -> R
): Flow<R> = combineUnsafe(flow, flow2, flow3, flow4, flow5) { args: Array<*> ->
    transform(
        args[0] as T1,
        args[1] as T2,
        args[2] as T3,
        args[3] as T4,
        args[4] as T5
    )
}

/**
 * Returns a [Flow] whose values are generated by [transform] function that process the most recently emitted values by each flow.
 *
 * The receiver of the [transform] is [FlowCollector] and thus `transform` is a
 * generic function that may transform emitted element, skip it or emit it multiple times.
 */
public fun <T1, T2, T3, T4, T5, R> combineTransform(
    flow: Flow<T1>,
    flow2: Flow<T2>,
    flow3: Flow<T3>,
    flow4: Flow<T4>,
    flow5: Flow<T5>,
    @BuilderInference transform: suspend FlowCollector<R>.(T1, T2, T3, T4, T5) -> Unit
): Flow<R> = combineTransformUnsafe(flow, flow2, flow3, flow4, flow5) { args: Array<*> ->
    transform(
        args[0] as T1,
        args[1] as T2,
        args[2] as T3,
        args[3] as T4,
        args[4] as T5
    )
}

/**
 * Returns a [Flow] whose values are generated with [transform] function by combining
 * the most recently emitted values by each flow.
 */
public inline fun <reified T, R> combine(
    vararg flows: Flow<T>,
    crossinline transform: suspend (Array<T>) -> R
): Flow<R> = flow {
    combineInternal(flows, { arrayOfNulls(flows.size) }, { emit(transform(it)) })
}

/**
 * Returns a [Flow] whose values are generated by [transform] function that process the most recently emitted values by each flow.
 *
 * The receiver of the [transform] is [FlowCollector] and thus `transform` is a
 * generic function that may transform emitted element, skip it or emit it multiple times.
 */
public inline fun <reified T, R> combineTransform(
    vararg flows: Flow<T>,
    @BuilderInference crossinline transform: suspend FlowCollector<R>.(Array<T>) -> Unit
): Flow<R> = safeFlow {
    combineInternal(flows, { arrayOfNulls(flows.size) }, { transform(it) })
}

/*
 * Same as combine, but does not copy array each time, deconstructing existing
 * array each time. Used in overloads that accept FunctionN instead of Function<Array<R>>
 */
private inline fun <reified T, R> combineUnsafe(
    vararg flows: Flow<T>,
    crossinline transform: suspend (Array<T>) -> R
): Flow<R> = flow {
    combineInternal(flows, nullArrayFactory(), { emit(transform(it)) })
}

/*
 * Same as combineTransform, but does not copy array each time, deconstructing existing
 * array each time. Used in overloads that accept FunctionN instead of Function<Array<R>>
 */
private inline fun <reified T, R> combineTransformUnsafe(
    vararg flows: Flow<T>,
    @BuilderInference crossinline transform: suspend FlowCollector<R>.(Array<T>) -> Unit
): Flow<R> = safeFlow {
    combineInternal(flows, nullArrayFactory(), { transform(it) })
}

// Saves bunch of anonymous classes
private fun <T> nullArrayFactory(): () -> Array<T>? = { null }

/**
 * Returns a [Flow] whose values are generated with [transform] function by combining
 * the most recently emitted values by each flow.
 */
public inline fun <reified T, R> combine(
    flows: Iterable<Flow<T>>,
    crossinline transform: suspend (Array<T>) -> R
): Flow<R> {
    val flowArray = flows.toList().toTypedArray()
    return flow {
        combineInternal(
            flowArray,
            arrayFactory = { arrayOfNulls(flowArray.size) },
            transform = { emit(transform(it)) })
    }
}

/**
 * Returns a [Flow] whose values are generated by [transform] function that process the most recently emitted values by each flow.
 *
 * The receiver of the [transform] is [FlowCollector] and thus `transform` is a
 * generic function that may transform emitted element, skip it or emit it multiple times.
 */
public inline fun <reified T, R> combineTransform(
    flows: Iterable<Flow<T>>,
    @BuilderInference crossinline transform: suspend FlowCollector<R>.(Array<T>) -> Unit
): Flow<R> {
    val flowArray = flows.toList().toTypedArray()
    return safeFlow {
        combineInternal(flowArray, { arrayOfNulls(flowArray.size) }, { transform(it) })
    }
}

/**
 * Zips values from the current flow (`this`) with [other] flow using provided [transform] function applied to each pair of values.
 * The resulting flow completes as soon as one of the flows completes and cancel is called on the remaining flow.
 *
 * It can be demonstrated with the following example:
 * ```
 * val flow = flowOf(1, 2, 3).onEach { delay(10) }
 * val flow2 = flowOf("a", "b", "c", "d").onEach { delay(15) }
 * flow.zip(flow2) { i, s -> i.toString() + s }.collect {
 *     println(it) // Will print "1a 2b 3c"
 * }
 * ```
 *
 * ### Buffering
 *
 * The upstream flow is collected sequentially in the same coroutine without any buffering, while the
 * [other] flow is collected concurrently as if `buffer(0)` is used. See documentation in the [buffer] operator
 * for explanation. You can use additional calls to the [buffer] operator as needed for more concurrency.
 */
public fun <T1, T2, R> Flow<T1>.zip(other: Flow<T2>, transform: suspend (T1, T2) -> R): Flow<R> = zipImpl(this, other, transform)
