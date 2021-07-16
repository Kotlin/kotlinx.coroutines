/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.selects.*
import kotlin.jvm.*
import kotlin.time.*

/* Scaffolding for Knit code examples
<!--- TEST_NAME FlowDelayTest -->
<!--- PREFIX .*-duration-.*
@file:OptIn(ExperimentalTime::class)
----- INCLUDE .*-duration-.*
import kotlin.time.*
----- INCLUDE .*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun main() = runBlocking {
----- SUFFIX .*
.toList().joinToString().let { println(it) } }
-->
*/

/**
 * Returns a flow that mirrors the original flow, but filters out values
 * that are followed by the newer values within the given [timeout][timeoutMillis].
 * The latest value is always emitted.
 *
 * Example:
 *
 * ```kotlin
 * flow {
 *     emit(1)
 *     delay(90)
 *     emit(2)
 *     delay(90)
 *     emit(3)
 *     delay(1010)
 *     emit(4)
 *     delay(1010)
 *     emit(5)
 * }.debounce(1000)
 * ```
 * <!--- KNIT example-delay-01.kt -->
 *
 * produces the following emissions
 *
 * ```text
 * 3, 4, 5
 * ```
 * <!--- TEST -->
 *
 * Note that the resulting flow does not emit anything as long as the original flow emits
 * items faster than every [timeoutMillis] milliseconds.
 */
@FlowPreview
public fun <T> Flow<T>.debounce(timeoutMillis: Long): Flow<T> {
    require(timeoutMillis >= 0L) { "Debounce timeout should not be negative" }
    if (timeoutMillis == 0L) return this
    return debounceInternal { timeoutMillis }
}

/**
 * Returns a flow that mirrors the original flow, but filters out values
 * that are followed by the newer values within the given [timeout][timeoutMillis].
 * The latest value is always emitted.
 *
 * A variation of [debounce] that allows specifying the timeout value dynamically.
 *
 * Example:
 *
 * ```kotlin
 * flow {
 *     emit(1)
 *     delay(90)
 *     emit(2)
 *     delay(90)
 *     emit(3)
 *     delay(1010)
 *     emit(4)
 *     delay(1010)
 *     emit(5)
 * }.debounce {
 *     if (it == 1) {
 *         0L
 *     } else {
 *         1000L
 *     }
 * }
 * ```
 * <!--- KNIT example-delay-02.kt -->
 *
 * produces the following emissions
 *
 * ```text
 * 1, 3, 4, 5
 * ```
 * <!--- TEST -->
 *
 * Note that the resulting flow does not emit anything as long as the original flow emits
 * items faster than every [timeoutMillis] milliseconds.
 *
 * @param timeoutMillis [T] is the emitted value and the return value is timeout in milliseconds.
 */
@FlowPreview
@OptIn(kotlin.experimental.ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
public fun <T> Flow<T>.debounce(timeoutMillis: (T) -> Long): Flow<T> =
    debounceInternal(timeoutMillis)

/**
 * Returns a flow that mirrors the original flow, but filters out values
 * that are followed by the newer values within the given [timeout].
 * The latest value is always emitted.
 *
 * Example:
 *
 * ```kotlin
 * flow {
 *     emit(1)
 *     delay(90.milliseconds)
 *     emit(2)
 *     delay(90.milliseconds)
 *     emit(3)
 *     delay(1010.milliseconds)
 *     emit(4)
 *     delay(1010.milliseconds)
 *     emit(5)
 * }.debounce(1000.milliseconds)
 * ```
 * <!--- KNIT example-delay-duration-01.kt -->
 *
 * produces the following emissions
 *
 * ```text
 * 3, 4, 5
 * ```
 * <!--- TEST -->
 *
 * Note that the resulting flow does not emit anything as long as the original flow emits
 * items faster than every [timeout] milliseconds.
 */
@ExperimentalTime
@FlowPreview
public fun <T> Flow<T>.debounce(timeout: Duration): Flow<T> =
    debounce(timeout.toDelayMillis())

/**
 * Returns a flow that mirrors the original flow, but filters out values
 * that are followed by the newer values within the given [timeout].
 * The latest value is always emitted.
 *
 * A variation of [debounce] that allows specifying the timeout value dynamically.
 *
 * Example:
 *
 * ```kotlin
 * flow {
 *     emit(1)
 *     delay(90.milliseconds)
 *     emit(2)
 *     delay(90.milliseconds)
 *     emit(3)
 *     delay(1010.milliseconds)
 *     emit(4)
 *     delay(1010.milliseconds)
 *     emit(5)
 * }.debounce {
 *     if (it == 1) {
 *         0.milliseconds
 *     } else {
 *         1000.milliseconds
 *     }
 * }
 * ```
 * <!--- KNIT example-delay-duration-02.kt -->
 *
 * produces the following emissions
 *
 * ```text
 * 1, 3, 4, 5
 * ```
 * <!--- TEST -->
 *
 * Note that the resulting flow does not emit anything as long as the original flow emits
 * items faster than every [timeout] unit.
 *
 * @param timeout [T] is the emitted value and the return value is timeout in [Duration].
 */
@ExperimentalTime
@FlowPreview
@JvmName("debounceDuration")
@OptIn(kotlin.experimental.ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
public fun <T> Flow<T>.debounce(timeout: (T) -> Duration): Flow<T> =
    debounceInternal { emittedItem ->
        timeout(emittedItem).toDelayMillis()
    }

private fun <T> Flow<T>.debounceInternal(timeoutMillisSelector: (T) -> Long) : Flow<T> =
    scopedFlow { downstream ->
        // Produce the values using the default (rendezvous) channel
        val values = produce {
            collect { value -> send(value ?: NULL) }
        }
        // Now consume the values
        var lastValue: Any? = null
        while (lastValue !== DONE) {
            var timeoutMillis = 0L // will be always computed when lastValue != null
            // Compute timeout for this value
            if (lastValue != null) {
                timeoutMillis = timeoutMillisSelector(NULL.unbox(lastValue))
                require(timeoutMillis >= 0L) { "Debounce timeout should not be negative" }
                if (timeoutMillis == 0L) {
                    downstream.emit(NULL.unbox(lastValue))
                    lastValue = null // Consume the value
                }
            }
            // assert invariant: lastValue != null implies timeoutMillis > 0
            assert { lastValue == null || timeoutMillis > 0 }
            // wait for the next value with timeout
            select<Unit> {
                // Set timeout when lastValue exists and is not consumed yet
                if (lastValue != null) {
                    onTimeout(timeoutMillis) {
                        downstream.emit(NULL.unbox(lastValue))
                        lastValue = null // Consume the value
                    }
                }
                values.onReceiveCatching { value ->
                    value
                        .onSuccess { lastValue = it }
                        .onFailure {
                            it?.let { throw it }
                            // If closed normally, emit the latest value
                            if (lastValue != null) downstream.emit(NULL.unbox(lastValue))
                            lastValue = DONE
                        }
                }
            }
        }
    }

/**
 * Returns a flow that emits only the latest value emitted by the original flow during the given sampling [period][periodMillis].
 *
 * Example:
 *
 * ```kotlin
 * flow {
 *     repeat(10) {
 *         emit(it)
 *         delay(110)
 *     }
 * }.sample(200)
 * ```
 * <!--- KNIT example-delay-03.kt -->
 *
 * produces the following emissions
 *
 * ```text
 * 1, 3, 5, 7, 9
 * ```
 * <!--- TEST -->
 *
 * Note that the latest element is not emitted if it does not fit into the sampling window.
 */
@FlowPreview
public fun <T> Flow<T>.sample(periodMillis: Long): Flow<T> {
    require(periodMillis > 0) { "Sample period should be positive" }
    return scopedFlow { downstream ->
        val values = produce(capacity = Channel.CONFLATED) {
            collect { value -> send(value ?: NULL) }
        }
        var lastValue: Any? = null
        val ticker = fixedPeriodTicker(periodMillis)
        while (lastValue !== DONE) {
            select<Unit> {
                values.onReceiveCatching { result ->
                    result
                        .onSuccess { lastValue = it }
                        .onFailure {
                            it?.let { throw it }
                            ticker.cancel(ChildCancelledException())
                            lastValue = DONE
                        }
                }

                // todo: shall be start sampling only when an element arrives or sample aways as here?
                ticker.onReceive {
                    val value = lastValue ?: return@onReceive
                    lastValue = null // Consume the value
                    downstream.emit(NULL.unbox(value))
                }
            }
        }
    }
}

/*
 * TODO this design (and design of the corresponding operator) depends on #540
 */
internal fun CoroutineScope.fixedPeriodTicker(delayMillis: Long, initialDelayMillis: Long = delayMillis): ReceiveChannel<Unit> {
    require(delayMillis >= 0) { "Expected non-negative delay, but has $delayMillis ms" }
    require(initialDelayMillis >= 0) { "Expected non-negative initial delay, but has $initialDelayMillis ms" }
    return produce(capacity = 0) {
        delay(initialDelayMillis)
        while (true) {
            channel.send(Unit)
            delay(delayMillis)
        }
    }
}

/**
 * Returns a flow that emits only the latest value emitted by the original flow during the given sampling [period].
 *
 * Example:
 *
 * ```kotlin
 * flow {
 *     repeat(10) {
 *         emit(it)
 *         delay(110.milliseconds)
 *     }
 * }.sample(200.milliseconds)
 * ```
 * <!--- KNIT example-delay-duration-03.kt -->
 *
 * produces the following emissions
 *
 * ```text
 * 1, 3, 5, 7, 9
 * ```
 * <!--- TEST -->
 *
 * Note that the latest element is not emitted if it does not fit into the sampling window.
 */
@ExperimentalTime
@FlowPreview
public fun <T> Flow<T>.sample(period: Duration): Flow<T> = sample(period.toDelayMillis())

/**
 * Returns a flow that mirrors the source flow, but filters out values
 * that follow an emitted value for the given [duration][timeoutMillis].
 * This ensures that at most one value is emitted in [the specified time window][timeoutMillis].
 * The first value is always emitted immediately.
 *
 * Example:
 * ```
 * flow {
 *     emit(1)
 *     delay(90)
 *     emit(2)
 *     delay(90)
 *     emit(3)
 *     delay(1010)
 *     emit(4)
 *     delay(1010)
 *     emit(5)
 * }.throttleFirst(1000)
 * ```
 * produces `1, 4, 5`.
 */
@FlowPreview
public fun <T> Flow<T>.throttleFirst(timeoutMillis: Long): Flow<T> {
    require(timeoutMillis > 0) { "Throttle timeout should be positive" }
    return scopedFlow { downstream ->
        val values = produce<Any?> {
            // Actually Any, KT-30796
            collect { send(it ?: NULL) }
        }

        var done = false
        var ignoreValuesWindow: Job? = null

        while (!done) {
            select<Unit> {
                values.onReceiveOrNull {
                    if (it == null) {
                        done = true
                        ignoreValuesWindow?.cancel(ChildCancelledException())
                    } else if (ignoreValuesWindow == null) {
                        downstream.emit(NULL.unbox(it))
                        ignoreValuesWindow = launch {
                            delay(timeoutMillis)
                        }
                    }
                }

                ignoreValuesWindow?.onJoin?.invoke {
                    ignoreValuesWindow = null
                }
            }
        }
    }
}

/**
 * Returns a flow that mirrors the source flow, but filters out values
 * that follow an emitted value for the given [duration][timeout].
 * This ensures that at most one value is emitted in [the specified time window][timeout].
 * The first value is always emitted immediately.
 *
 * Example:
 * ```
 * flow {
 *     emit(1)
 *     delay(90)
 *     emit(2)
 *     delay(90)
 *     emit(3)
 *     delay(1010)
 *     emit(4)
 *     delay(1010)
 *     emit(5)
 * }.throttleFirst(1000.milliseconds)
 * ```
 * produces `1, 4, 5`.
 */
@ExperimentalTime
@FlowPreview
public fun <T> Flow<T>.throttleFirst(timeout: Duration): Flow<T> {
    return throttleFirst(timeout.toDelayMillis())
}

/**
 * Returns a flow that mirrors the source flow, but conflates values so that
 * at most one value is emitted by time window of a given [duration][windowMillis].
 * The first is always emitted immediately ; subsequent values may be delayed depending on the source's pace.
 * If the source terminates while a value is being delayed (due to having already emitted a value in its time window),
 * then that value is *not* emitted when the flow terminates.
 *
 * Example:
 * ```
 * flow {
 *  emit(1)
 *  delay(120)
 *  emit(2)
 *  delay(60)
 *  emit(3)
 *  delay(60)
 *  emit(4)
 *  delay(60)
 *  emit(5)
 *  delay(200)
 *  emit(6)
 *  delay(50)
 *  emit(7)
 * }.throttleLatest(100)
 *  ```
 *  produces
 *  - `1` immediately,
 *  - `2` after 100ms,
 *  - `3` after 200ms (delayed by 40ms),
 *  - `5` after 300ms (delayed by 20ms),
 *  - `7` after 500ms.
 */
@FlowPreview
public fun <T> Flow<T>.throttleLatest(windowMillis: Long): Flow<T> {
    require(windowMillis > 0) { "Throttle window should be positive" }
    return scopedFlow { downstream ->
        val values = produce<Any?> {
            // Actually Any, KT-30796
            collect { send(it ?: NULL) }
        }

        val timeWindows = fixedPeriodTicker(windowMillis, 0)
        var latestValue: Any? = null

        while (latestValue !== DONE) {
            select<Unit> {
                if (latestValue != null) {
                    timeWindows.onReceive {
                        downstream.emit(NULL.unbox(latestValue))
                        latestValue = null
                    }
                }

                values.onReceiveOrNull {
                    if (it == null) {
                        latestValue = DONE
                        timeWindows.cancel(ChildCancelledException())
                    } else {
                        latestValue = it
                    }
                }
            }
        }
    }
}

/**
 * Returns a flow that mirrors the source flow, but conflates values so that
 * at most one value is emitted by time window of a given [duration][window].
 * The first value is always emitted immediately ; subsequent values may be delayed depending on the source's pace.
 * If the source terminates while a value is being delayed (due to having already emitted a value in its time window),
 * then that value is *not* emitted when the flow terminates.
 *
 * Example:
 * ```
 * flow {
 *  emit(1)
 *  delay(120.milliseconds)
 *  emit(2)
 *  delay(60.milliseconds)
 *  emit(3)
 *  delay(60.milliseconds)
 *  emit(4)
 *  delay(60.milliseconds)
 *  emit(5)
 *  delay(200.milliseconds)
 *  emit(6)
 *  delay(50.milliseconds)
 *  emit(7)
 * }.throttleLatest(100.milliseconds)
 *  ```
 *  produces
 *  - `1` immediately,
 *  - `2` after 100ms,
 *  - `3` after 200ms (delayed by 40ms),
 *  - `5` after 300ms (delayed by 20ms),
 *  - `7` after 500ms.
 */
@ExperimentalTime
@FlowPreview
public fun <T> Flow<T>.throttleLatest(window: Duration): Flow<T> {
    return throttleLatest(window.toDelayMillis())
}
