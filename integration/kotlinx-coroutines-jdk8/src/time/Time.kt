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
        kotlinx.coroutines.delay(duration.toNanos(), TimeUnit.NANOSECONDS)

/**
 * "java.time" adapter method for [SelectBuilder.onTimeout]
 */
public suspend fun <R> SelectBuilder<R>.onTimeout(duration: Duration, block: suspend () -> R) =
        onTimeout(duration.toNanos(), TimeUnit.NANOSECONDS, block)

/**
 * "java.time" adapter method for [kotlinx.coroutines.withTimeout]
 */
public suspend fun <T> withTimeout(duration: Duration, block: suspend CoroutineScope.() -> T): T =
        kotlinx.coroutines.withTimeout(duration.toNanos(), TimeUnit.NANOSECONDS, block)

/**
 * @suppress **Deprecated**: for binary compatibility only
 */
@Deprecated("for binary compatibility only", level=DeprecationLevel.HIDDEN)
public suspend fun <T> withTimeout(duration: Duration, block: suspend () -> T): T =
        kotlinx.coroutines.withTimeout(duration.toNanos(), TimeUnit.NANOSECONDS) { block() }

/**
 * "java.time" adapter method for [kotlinx.coroutines.withTimeoutOrNull]
 */
public suspend fun <T> withTimeoutOrNull(duration: Duration, block: suspend CoroutineScope.() -> T): T? =
        kotlinx.coroutines.withTimeoutOrNull(duration.toNanos(), TimeUnit.NANOSECONDS, block)

/**
 * @suppress **Deprecated**: for binary compatibility only
 */
@Deprecated("for binary compatibility only", level=DeprecationLevel.HIDDEN)
public suspend fun <T> withTimeoutOrNull(duration: Duration, block: suspend () -> T): T? =
        kotlinx.coroutines.withTimeoutOrNull(duration.toNanos(), TimeUnit.NANOSECONDS) { block() }
