/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.jdk9

import kotlinx.coroutines.*
import java.util.concurrent.*
import org.reactivestreams.FlowAdapters
import kotlinx.coroutines.reactive.*

/**
 * Awaits the first value from the given publisher without blocking the thread and returns the resulting value, or, if
 * the publisher has produced an error, throws the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Flow.Subscription] and resumes with [CancellationException].
 *
 * @throws NoSuchElementException if the publisher does not emit any value
 */
public suspend fun <T> Flow.Publisher<T>.awaitFirst(): T =
    FlowAdapters.toPublisher(this).awaitFirst()

/**
 * Awaits the first value from the given publisher, or returns the [default] value if none is emitted, without blocking
 * the thread, and returns the resulting value, or, if this publisher has produced an error, throws the corresponding
 * exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Flow.Subscription] and resumes with [CancellationException].
 */
public suspend fun <T> Flow.Publisher<T>.awaitFirstOrDefault(default: T): T =
    FlowAdapters.toPublisher(this).awaitFirstOrDefault(default)

/**
 * Awaits the first value from the given publisher, or returns `null` if none is emitted, without blocking the thread,
 * and returns the resulting value, or, if this publisher has produced an error, throws the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Flow.Subscription] and resumes with [CancellationException].
 */
public suspend fun <T> Flow.Publisher<T>.awaitFirstOrNull(): T? =
    FlowAdapters.toPublisher(this).awaitFirstOrNull()

/**
 * Awaits the first value from the given publisher, or calls [defaultValue] to get a value if none is emitted, without
 * blocking the thread, and returns the resulting value, or, if this publisher has produced an error, throws the
 * corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Flow.Subscription] and resumes with [CancellationException].
 */
public suspend fun <T> Flow.Publisher<T>.awaitFirstOrElse(defaultValue: () -> T): T =
    FlowAdapters.toPublisher(this).awaitFirstOrElse(defaultValue)

/**
 * Awaits the last value from the given publisher without blocking the thread and
 * returns the resulting value, or, if this publisher has produced an error, throws the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Flow.Subscription] and resumes with [CancellationException].
 *
 * @throws NoSuchElementException if the publisher does not emit any value
 */
public suspend fun <T> Flow.Publisher<T>.awaitLast(): T =
    FlowAdapters.toPublisher(this).awaitLast()

/**
 * Awaits the single value from the given publisher without blocking the thread and returns the resulting value, or,
 * if this publisher has produced an error, throws the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Flow.Subscription] and resumes with [CancellationException].
 *
 * @throws NoSuchElementException if the publisher does not emit any value
 * @throws IllegalArgumentException if the publisher emits more than one value
 */
public suspend fun <T> Flow.Publisher<T>.awaitSingle(): T =
    FlowAdapters.toPublisher(this).awaitSingle()
