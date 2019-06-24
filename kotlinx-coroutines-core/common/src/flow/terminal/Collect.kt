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
 * This operator is usually used with [onEach] and [catch] operators to process all emitted values and
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
 * Collects all the values from the given [flow] and emits them to the collector.
 * 
 * It is a shorthand for `flow.collect { value -> emit(value) }`.
 */
@ExperimentalCoroutinesApi
public suspend inline fun <T> FlowCollector<T>.emitAll(flow: Flow<T>) = flow.collect(this)
