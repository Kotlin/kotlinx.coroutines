/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:OptIn(ExperimentalContracts::class)

package kotlinx.coroutines.time

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.selects.*
import java.time.*
import java.time.temporal.*
import kotlin.contracts.*

/**
 * "java.time" adapter method for [kotlinx.coroutines.delay].
 */
public suspend fun delay(duration: Duration): Unit = delay(duration.coerceToMillis())

/**
 * "java.time" adapter method for [kotlinx.coroutines.flow.debounce].
 */
@FlowPreview
public fun <T> Flow<T>.debounce(timeout: Duration): Flow<T> = debounce(timeout.coerceToMillis())

/**
 * "java.time" adapter method for [kotlinx.coroutines.flow.sample].
 */
@FlowPreview
public fun <T> Flow<T>.sample(period: Duration): Flow<T> = sample(period.coerceToMillis())

/**
 * "java.time" adapter method for [SelectBuilder.onTimeout].
 */
public fun <R> SelectBuilder<R>.onTimeout(duration: Duration, block: suspend () -> R): Unit =
        onTimeout(duration.coerceToMillis(), block)

/**
 * "java.time" adapter method for [kotlinx.coroutines.withTimeout].
 */
public suspend fun <T> withTimeout(duration: Duration, block: suspend CoroutineScope.() -> T): T {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    return kotlinx.coroutines.withTimeout(duration.coerceToMillis(), block)
}

/**
 * "java.time" adapter method for [kotlinx.coroutines.withTimeoutOrNull].
 */
public suspend fun <T> withTimeoutOrNull(duration: Duration, block: suspend CoroutineScope.() -> T): T? =
        kotlinx.coroutines.withTimeoutOrNull(duration.coerceToMillis(), block)

/**
 * Coerces the given [Duration] to a millisecond delay.
 * Negative values are coerced to zero, values that cannot
 * be represented in milliseconds as long ("infinite" duration) are coerced to [Long.MAX_VALUE]
 * and durations lesser than a millisecond are coerced to 1 millisecond.
 *
 * The rationale of coercion:
 * 1) Too large durations typically indicate infinity and Long.MAX_VALUE is the
 *    best approximation of infinity we can provide.
 * 2) Coercing too small durations to 1 instead of 0 is crucial for two patterns:
 *    - Programming with deadlines and delays
 *    - Non-suspending fast-paths (e.g. `withTimeout(1 nanosecond) { 42 }` should not throw)
 */
private fun Duration.coerceToMillis(): Long {
    if (this <= Duration.ZERO) return 0
    if (this <= ChronoUnit.MILLIS.duration) return 1

    // Maximum scalar values of Duration.ofMillis(Long.MAX_VALUE)
    val maxSeconds = 9223372036854775
    val maxNanos = 807000000
    return if (seconds < maxSeconds || seconds == maxSeconds && nano < maxNanos) toMillis()
    else Long.MAX_VALUE
}
