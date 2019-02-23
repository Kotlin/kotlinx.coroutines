/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.time

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.selects.SelectBuilder
import java.time.Duration
import java.time.temporal.ChronoUnit

/**
 * "java.time" adapter method for [kotlinx.coroutines.delay]
 */
public suspend fun delay(duration: Duration) =
        kotlinx.coroutines.delay(duration.toMillisDelay())

/**
 * "java.time" adapter method for [SelectBuilder.onTimeout]
 */
public fun <R> SelectBuilder<R>.onTimeout(duration: Duration, block: suspend () -> R) =
        onTimeout(duration.toMillisDelay(), block)

/**
 * "java.time" adapter method for [kotlinx.coroutines.withTimeout]
 */
public suspend fun <T> withTimeout(duration: Duration, block: suspend CoroutineScope.() -> T): T =
        kotlinx.coroutines.withTimeout(duration.toMillisDelay(), block)

/**
 * "java.time" adapter method for [kotlinx.coroutines.withTimeoutOrNull]
 */
public suspend fun <T> withTimeoutOrNull(duration: Duration, block: suspend CoroutineScope.() -> T): T? =
        kotlinx.coroutines.withTimeoutOrNull(duration.toMillisDelay(), block)

/**
 * Convert the [Duration] to millisecond delay.
 *
 * @return strictly positive duration is coerced to 1..[Long.MAX_VALUE] ms, `0` otherwise.
 */
private fun Duration.toMillisDelay(): Long =
        if (this <= ChronoUnit.MILLIS.duration) {
            if (this <= Duration.ZERO) 0
            else 1
        } else {
            // values of Duration.ofMillis(Long.MAX_VALUE)
            val maxSeconds = 9223372036854775
            val maxNanos = 807000000
            if (seconds < maxSeconds || seconds == maxSeconds && nano < maxNanos) toMillis()
            else Long.MAX_VALUE
        }
