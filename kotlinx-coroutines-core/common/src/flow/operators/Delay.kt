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
import kotlinx.coroutines.flow.unsafeFlow as flow

/**
 * Delays the emission of values from this flow for the given [timeMillis].
 */
@FlowPreview
public fun <T> Flow<T>.delayFlow(timeMillis: Long): Flow<T> = flow {
    delay(timeMillis)
    collect(this@flow)
}

/**
 * Delays each element emitted by the given flow for the given [timeMillis].
 */
@FlowPreview
public fun <T> Flow<T>.delayEach(timeMillis: Long): Flow<T> = flow {
    collect { value ->
        delay(timeMillis)
        emit(value)
    }
}

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
public fun <T> Flow<T>.debounce(timeoutMillis: Long): Flow<T> {
    require(timeoutMillis > 0) { "Debounce timeout should be positive" }
    return flow {
        coroutineScope {
            val values = Channel<Any?>(Channel.CONFLATED) // Actually Any, KT-30796
            // Channel is not closed deliberately as there is no close with value
            val collector = launch {
                try {
                    collect { value -> values.send(value ?: NullSurrogate) }
                } catch (e: Throwable) {
                    values.close(e) // Workaround for #1130
                    throw e
                }
            }

            var isDone = false
            var lastValue: Any? = null
            while (!isDone) {
                select<Unit> {
                    values.onReceive {
                        lastValue = it
                    }

                    lastValue?.let { value -> // set timeout when lastValue != null
                        onTimeout(timeoutMillis) {
                            lastValue = null // Consume the value
                            emit(NullSurrogate.unbox(value))
                        }
                    }

                    // Close with value 'idiom'
                    collector.onJoin {
                        if (lastValue != null) emit(NullSurrogate.unbox(lastValue))
                        isDone = true
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
public fun <T> Flow<T>.sample(periodMillis: Long): Flow<T> {
    require(periodMillis > 0) { "Sample period should be positive" }
    return flow {
        coroutineScope {
            val values = produce<Any?>(capacity = Channel.CONFLATED) {  // Actually Any, KT-30796
                collect { value -> send(value ?: NullSurrogate) }
            }

            var isDone = false
            var lastValue: Any? = null
            val ticker = fixedPeriodTicker(periodMillis)
            while (!isDone) {
                select<Unit> {
                    values.onReceiveOrNull {
                        if (it == null) {
                            ticker.cancel()
                            isDone = true
                        } else {
                            lastValue = it
                        }
                    }

                    // todo: shall be start sampling only when an element arrives or sample aways as here?
                    ticker.onReceive {
                        val value = lastValue ?: return@onReceive
                        lastValue = null // Consume the value
                        emit(NullSurrogate.unbox(value))
                    }
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
