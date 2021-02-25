/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.internal.*
import kotlin.jvm.*

/**
 * Terminal flow operator that collects the given flow but ignores all emitted values.
 * If any exception occurs during collect or in the provided flow, this exception is rethrown from this method.
 *
 * It is a shorthand for `collect {}`.
 *
 * This operator is usually used with [onEach], [onCompletion] and [catch] operators to process all emitted values and
 * handle an exception that might occur in the upstream flow or during processing, for example:
 *
 * ```
 * flow
 *     .onEach { value -> process(value) }
 *     .catch { e -> handleException(e) }
 *     .collect() // trigger collection of the flow
 * ```
 */
public suspend fun Flow<*>.collect(): Unit = collect(NopCollector)

/**
 * Terminal flow operator that [launches][launch] the [collection][collect] of the given flow in the [scope].
 * It is a shorthand for `scope.launch { flow.collect() }`.
 *
 * This operator is usually used with [onEach], [onCompletion] and [catch] operators to process all emitted values
 * handle an exception that might occur in the upstream flow or during processing, for example:
 *
 * ```
 * flow
 *     .onEach { value -> updateUi(value) }
 *     .onCompletion { cause -> updateUi(if (cause == null) "Done" else "Failed") }
 *     .catch { cause -> LOG.error("Exception: $cause") }
 *     .launchIn(uiScope)
 * ```
 *
 * Note that resulting value of [launchIn] is not used the provided scope takes care of cancellation.
 */
public fun <T> Flow<T>.launchIn(scope: CoroutineScope): Job = scope.launch {
    collect() // tail-call
}

/**
 * Terminal flow operator that collects the given flow with a provided [action].
 * If any exception occurs during collect or in the provided flow, this exception is rethrown from this method.
 *
 * Example of use:
 *
 * ```
 * val flow = getMyEvents()
 * try {
 *     flow.collect { value ->
 *         println("Received $value")
 *     }
 *     println("My events are consumed successfully")
 * } catch (e: Throwable) {
 *     println("Exception from the flow: $e")
 * }
 * ```
 */
public suspend inline fun <T> Flow<T>.collect(crossinline action: suspend (value: T) -> Unit): Unit =
    collect(object : FlowCollector<T> {
        override suspend fun emit(value: T) = action(value)
    })

/**
 * Terminal flow operator that collects the given flow with a provided [action] that takes the index of an element (zero-based) and the element.
 * If any exception occurs during collect or in the provided flow, this exception is rethrown from this method.
 *
 * See also [collect] and [withIndex].
 */
public suspend inline fun <T> Flow<T>.collectIndexed(crossinline action: suspend (index: Int, value: T) -> Unit): Unit =
    collect(object : FlowCollector<T> {
        private var index = 0
        override suspend fun emit(value: T) = action(checkIndexOverflow(index++), value)
    })

/**
 * Terminal flow operator that collects the given flow with a provided [action].
 * The crucial difference from [collect] is that when the original flow emits a new value
 * then the [action] block for the previous value is cancelled.
 *
 * It can be demonstrated by the following example:
 *
 * ```
 * flow {
 *     emit(1)
 *     delay(50)
 *     emit(2)
 * }.collectLatest { value ->
 *     println("Collecting $value")
 *     delay(100) // Emulate work
 *     println("$value collected")
 * }
 * ```
 *
 * prints "Collecting 1, Collecting 2, 2 collected"
 */
public suspend fun <T> Flow<T>.collectLatest(action: suspend (value: T) -> Unit) {
    /*
     * Implementation note:
     * buffer(0) is inserted here to fulfil user's expectations in sequential usages, e.g.:
     * ```
     * flowOf(1, 2, 3).collectLatest {
     *     delay(1)
     *     println(it) // Expect only 3 to be printed
     * }
     * ```
     *
     * It's not the case for intermediate operators which users mostly use for interactive UI,
     * where performance of dispatch is more important.
     */
    mapLatest(action).buffer(0).collect()
}

/**
 * Collects all the values from the given [flow] and emits them to the collector.
 * It is a shorthand for `flow.collect { value -> emit(value) }`.
 */
@BuilderInference
public suspend inline fun <T> FlowCollector<T>.emitAll(flow: Flow<T>): Unit = flow.collect(this)
