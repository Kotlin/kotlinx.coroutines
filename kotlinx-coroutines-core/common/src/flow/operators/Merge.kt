/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")
@file:Suppress("unused")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.internal.*
import kotlin.jvm.*
import kotlinx.coroutines.flow.internal.unsafeFlow as flow

/**
 * Name of the property that defines the value of [DEFAULT_CONCURRENCY].
 */
@FlowPreview
public const val DEFAULT_CONCURRENCY_PROPERTY_NAME = "kotlinx.coroutines.flow.defaultConcurrency"

/**
 * Default concurrency limit that is used by [flattenMerge] and [flatMapMerge] operators.
 * It is 16 by default and can be changed on JVM using [DEFAULT_CONCURRENCY_PROPERTY_NAME] property.
 */
@FlowPreview
public val DEFAULT_CONCURRENCY = systemProp(DEFAULT_CONCURRENCY_PROPERTY_NAME,
    16, 1, Int.MAX_VALUE
)

/**
 * Transforms elements emitted by the original flow by applying [transform], that returns another flow,
 * and then concatenating and flattening these flows.
 *
 * This method is is a shortcut for `map(transform).flattenConcat()`. See [flattenConcat].
 *
 * Note that even though this operator looks very familiar, we discourage its usage in a regular application-specific flows.
 * Most likely, suspending operation in [map] operator will be sufficient and linear transformations are much easier to reason about.
 */
@FlowPreview
public fun <T, R> Flow<T>.flatMapConcat(transform: suspend (value: T) -> Flow<R>): Flow<R> =
    map(transform).flattenConcat()

/**
 * Transforms elements emitted by the original flow by applying [transform], that returns another flow,
 * and then merging and flattening these flows.
 *
 * This operator calls [transform] *sequentially* and then merges the resulting flows with a [concurrency]
 * limit on the number of concurrently collected flows.
 * It is a shortcut for `map(transform).flattenMerge(concurrency)`.
 * See [flattenMerge] for details.
 *
 * Note that even though this operator looks very familiar, we discourage its usage in a regular application-specific flows.
 * Most likely, suspending operation in [map] operator will be sufficient and linear transformations are much easier to reason about.
 *
 * ### Operator fusion
 *
 * Applications of [flowOn], [buffer], [produceIn], and [broadcastIn] _after_ this operator are fused with
 * its concurrent merging so that only one properly configured channel is used for execution of merging logic.
 *
 * @param concurrency controls the number of in-flight flows, at most [concurrency] flows are collected
 * at the same time. By default it is equal to [DEFAULT_CONCURRENCY].
 */
@FlowPreview
public fun <T, R> Flow<T>.flatMapMerge(
    concurrency: Int = DEFAULT_CONCURRENCY,
    transform: suspend (value: T) -> Flow<R>
): Flow<R> =
    map(transform).flattenMerge(concurrency)

/**
 * Flattens the given flow of flows into a single flow in a sequentially manner, without interleaving nested flows.
 * This method is conceptually identical to `flattenMerge(concurrency = 1)` but has faster implementation.
 *
 * Inner flows are collected by this operator *sequentially*.
 */
@FlowPreview
public fun <T> Flow<Flow<T>>.flattenConcat(): Flow<T> = flow {
    collect { value -> emitAll(value) }
}

/**
 * Flattens the given flow of flows into a single flow with a [concurrency] limit on the number of
 * concurrently collected flows.
 *
 * If [concurrency] is more than 1, then inner flows are be collected by this operator *concurrently*.
 * With `concurrency == 1` this operator is identical to [flattenConcat].
 *
 * ### Operator fusion
 *
 * Applications of [flowOn], [buffer], [produceIn], and [broadcastIn] _after_ this operator are fused with
 * its concurrent merging so that only one properly configured channel is used for execution of merging logic.
 *
 * @param concurrency controls the number of in-flight flows, at most [concurrency] flows are collected
 * at the same time. By default it is equal to [DEFAULT_CONCURRENCY].
 */
@FlowPreview
public fun <T> Flow<Flow<T>>.flattenMerge(concurrency: Int = DEFAULT_CONCURRENCY): Flow<T> {
    require(concurrency > 0) { "Expected positive concurrency level, but had $concurrency" }
    return if (concurrency == 1) flattenConcat() else ChannelFlowMerge(this, concurrency)
}

/**
 * Returns a flow that produces element by [transform] function every time the original flow emits a value.
 * When the original flow emits a new value, the previous `transform` block is cancelled, thus the name `transformLatest`.
 *
 * For example, the following flow:
 * ```
 * flow {
 *     emit("a")
 *     delay(100)
 *     emit("b")
 * }.transformLatest { value ->
 *     emit(value)
 *     delay(200)
 *     emit(value + "_last")
 * }
 * ```
 * produces `a b b_last`.
 *
 * This operator is [buffered][buffer] by default and size of its output buffer can be changed by applying subsequent [buffer] operator.
 */
@ExperimentalCoroutinesApi
public fun <T, R> Flow<T>.transformLatest(@BuilderInference transform: suspend FlowCollector<R>.(value: T) -> Unit): Flow<R> =
    ChannelFlowTransformLatest(transform, this)

/**
 * Returns a flow that switches to a new flow produced by [transform] function every time the original flow emits a value.
 * When the original flow emits a new value, the previous flow produced by `transform` block is cancelled.
 *
 * For example, the following flow:
 * ```
 * flow {
 *     emit("a")
 *     delay(100)
 *     emit("b")
 * }.flatMapLatest { value ->
 *     flow {
 *         emit(value)
 *         delay(200)
 *         emit(value + "_last")
 *     }
 * }
 * ```
 * produces `a b b_last`
 *
 * This operator is [buffered][buffer] by default and size of its output buffer can be changed by applying subsequent [buffer] operator.
 */
@ExperimentalCoroutinesApi
public fun <T, R> Flow<T>.flatMapLatest(@BuilderInference transform: (value: T) -> Flow<R>): Flow<R> =
    transformLatest { emitAll(transform(it)) }

/**
 * Returns a flow that emits elements from the original flow transformed by [transform] function.
 * When the original flow emits a new value, computation of the [transform] block for previous value is cancelled.
 *
 * For example, the following flow:
 * ```
 * flow {
 *     emit("a")
 *     delay(100)
 *     emit("b")
 * }.mapLatest { value ->
 *     println("Started computing $value")
 *     delay(200)
 *     "Computed $value"
 * }
 * ```
 * will print "Started computing 1" and "Started computing 2", but the resulting flow will contain only "Computed 2" value.
 *
 * This operator is [buffered][buffer] by default and size of its output buffer can be changed by applying subsequent [buffer] operator.
 */
@ExperimentalCoroutinesApi
public fun <T, R> Flow<T>.mapLatest(@BuilderInference transform: suspend (value: T) -> R): Flow<R> =
    transformLatest { emit(transform(it)) }
