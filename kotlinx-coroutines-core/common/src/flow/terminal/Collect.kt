/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
@ExperimentalCoroutinesApi // tentatively stable in 1.3.0
public suspend fun Flow<*>.collect() = collect(NopCollector)

/**
 * Terminal flow operator that [launches][launch] the [collection][collect] of the given flow in the [scope].
 * It is a shorthand for `scope.launch { flow.collect() }`.
 *
 * This operator is usually used with [onEach], [onCompletion] and [catch] operators to process all emitted values
 * handle an exception that might occur in the upstream flow or during processing, for example:
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
@ExperimentalCoroutinesApi // tentatively stable in 1.3.0
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
@ExperimentalCoroutinesApi
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
@ExperimentalCoroutinesApi
public suspend inline fun <T> Flow<T>.collectIndexed(crossinline action: suspend (index: Int, value: T) -> Unit): Unit =
    collect(object : FlowCollector<T> {
        private var index = 0
        override suspend fun emit(value: T) = action(checkIndexOverflow(index++), value)
    })

/**
 * Collects all the values from the given [flow] and emits them to the collector.
 * 
 * It is a shorthand for `flow.collect { value -> emit(value) }`.
 */
@ExperimentalCoroutinesApi
public suspend inline fun <T> FlowCollector<T>.emitAll(flow: Flow<T>) = flow.collect(this)
