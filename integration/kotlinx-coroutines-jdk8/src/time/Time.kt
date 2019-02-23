/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.time

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.selects.SelectBuilder
import java.time.Duration
import kotlin.coroutines.suspendCoroutine

/**
 * "java.time" adapter method for [kotlinx.coroutines.delay]
 */
public suspend fun delay(duration: Duration) {
    if (duration.seconds < Long.MAX_VALUE / 1_000L) kotlinx.coroutines.delay(duration.toMillis())
    else suspendCoroutine<Unit> { }
}

/**
 * "java.time" adapter method for [SelectBuilder.onTimeout]
 */
public fun <R> SelectBuilder<R>.onTimeout(duration: Duration, block: suspend () -> R) {
    if (duration.seconds < Long.MAX_VALUE / 1_000L) onTimeout(duration.toMillis(), block)
}

/**
 * "java.time" adapter method for [kotlinx.coroutines.withTimeout]
 */
public suspend fun <T> withTimeout(duration: Duration, block: suspend CoroutineScope.() -> T): T =
        if (duration.seconds < Long.MAX_VALUE / 1_000L) kotlinx.coroutines.withTimeout(duration.toMillis(), block)
        else coroutineScope { block() }

/**
 * "java.time" adapter method for [kotlinx.coroutines.withTimeoutOrNull]
 */
public suspend fun <T> withTimeoutOrNull(duration: Duration, block: suspend CoroutineScope.() -> T): T? =
        if (duration.seconds < Long.MAX_VALUE / 1_000L) kotlinx.coroutines.withTimeoutOrNull(duration.toMillis(), block)
        else coroutineScope { block() }
