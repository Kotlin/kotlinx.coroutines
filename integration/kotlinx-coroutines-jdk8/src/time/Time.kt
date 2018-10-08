/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.time

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.selects.SelectBuilder
import java.time.Duration
import java.util.concurrent.TimeUnit

/**
 * "java.time" adapter method for [kotlinx.coroutines.delay]
 */
public suspend fun delay(duration: Duration) =
    kotlinx.coroutines.delay(duration.toMillis())

/**
 * "java.time" adapter method for [SelectBuilder.onTimeout]
 */
public fun <R> SelectBuilder<R>.onTimeout(duration: Duration, block: suspend () -> R) =
    onTimeout(duration.toMillis(), block)

/**
 * "java.time" adapter method for [kotlinx.coroutines.withTimeout]
 */
public suspend fun <T> withTimeout(duration: Duration, block: suspend CoroutineScope.() -> T): T =
    kotlinx.coroutines.withTimeout(duration.toMillis(), block)

/**
 * "java.time" adapter method for [kotlinx.coroutines.withTimeoutOrNull]
 */
public suspend fun <T> withTimeoutOrNull(duration: Duration, block: suspend CoroutineScope.() -> T): T? =
    kotlinx.coroutines.withTimeoutOrNull(duration.toMillis(), block)