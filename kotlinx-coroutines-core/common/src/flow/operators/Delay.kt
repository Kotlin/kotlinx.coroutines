/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.selects.*
import kotlin.jvm.*
import kotlinx.coroutines.flow.internal.unsafeFlow as flow

/**
 * Returns a flow that mirrors the original flow, but filters out values
 * that are followed by the newer values within the given [timeout][timeoutMillis].
 * The latest value is always emitted.
 *
 * Example:
 * ```
 * flow {
 *     emit(1)
 *     delay(99)
 *     emit(2)
 *     delay(99)
 *     emit(3)
 *     delay(1001)
 *     emit(4)
 *     delay(1001)
 *     emit(5)
 * }.debounce(1000)
 * ```
 * produces `3, 4, 5`.
 *
 * Note that the resulting flow does not emit anything as long as the original flow emits
 * items faster than every [timeoutMillis] milliseconds.
 */
@FlowPreview
public fun <T> Flow<T>.debounce(timeoutMillis: Long): Flow<T> {
    require(timeoutMillis > 0) { "Debounce timeout should be positive" }
    return scopedFlow { downstream ->
        // Actually Any, KT-30796
        val values = produce<Any?>(capacity = Channel.CONFLATED) {
            collect { value -> send(value ?: NULL) }
        }
        var lastValue: Any? = null
        while (lastValue !== DONE) {
            select<Unit> {
                // Should be receiveOrClosed when boxing issues are fixed
                values.onReceiveOrNull {
                    if (it == null) {
                        if (lastValue != null) downstream.emit(NULL.unbox(lastValue))
                        lastValue = DONE
                    } else {
                        lastValue = it
                    }
                }

                lastValue?.let { value ->
                    // set timeout when lastValue != null
                    onTimeout(timeoutMillis) {
                        lastValue = null // Consume the value
                        downstream.emit(NULL.unbox(value))
                    }
                }
            }
        }
    }
}

/**
 * Returns a flow that emits only the latest value emitted by the original flow during the given sampling [period][periodMillis].
 *
 * Example:
 * ```
 * flow {
 *     repeat(10) {
 *         emit(it)
 *         delay(50)
 *     }
 * }.sample(100)
 * ```
 * produces `1, 3, 5, 7, 9`.
 * 
 * Note that the latest element is not emitted if it does not fit into the sampling window.
 */
@FlowPreview
public fun <T> Flow<T>.sample(periodMillis: Long): Flow<T> {
    require(periodMillis > 0) { "Sample period should be positive" }
    return scopedFlow { downstream ->
        val values = produce<Any?>(capacity = Channel.CONFLATED) {
            // Actually Any, KT-30796
            collect { value -> send(value ?: NULL) }
        }
        var lastValue: Any? = null
        val ticker = fixedPeriodTicker(periodMillis)
        while (lastValue !== DONE) {
            select<Unit> {
                values.onReceiveOrNull {
                    if (it == null) {
                        ticker.cancel(ChildCancelledException())
                        lastValue = DONE
                    } else {
                        lastValue = it
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
