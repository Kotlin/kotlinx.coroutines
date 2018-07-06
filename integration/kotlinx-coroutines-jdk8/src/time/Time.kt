/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.experimental.time

import kotlinx.coroutines.experimental.CoroutineScope
import kotlinx.coroutines.experimental.selects.SelectBuilder
import java.time.Duration
import java.util.concurrent.TimeUnit

/**
 * "java.time" adapter method for [kotlinx.coroutines.experimental.delay]
 */
public suspend fun delay(duration: Duration) =
        kotlinx.coroutines.experimental.delay(duration.toNanos(), TimeUnit.NANOSECONDS)

/**
 * "java.time" adapter method for [SelectBuilder.onTimeout]
 */
public suspend fun <R> SelectBuilder<R>.onTimeout(duration: Duration, block: suspend () -> R) =
        onTimeout(duration.toNanos(), TimeUnit.NANOSECONDS, block)

/**
 * "java.time" adapter method for [kotlinx.coroutines.experimental.withTimeout]
 */
public suspend fun <T> withTimeout(duration: Duration, block: suspend CoroutineScope.() -> T): T =
        kotlinx.coroutines.experimental.withTimeout(duration.toNanos(), TimeUnit.NANOSECONDS, block)

/**
 * @suppress **Deprecated**: for binary compatibility only
 */
@Deprecated("for binary compatibility only", level=DeprecationLevel.HIDDEN)
public suspend fun <T> withTimeout(duration: Duration, block: suspend () -> T): T =
        kotlinx.coroutines.experimental.withTimeout(duration.toNanos(), TimeUnit.NANOSECONDS) { block() }

/**
 * "java.time" adapter method for [kotlinx.coroutines.experimental.withTimeoutOrNull]
 */
public suspend fun <T> withTimeoutOrNull(duration: Duration, block: suspend CoroutineScope.() -> T): T? =
        kotlinx.coroutines.experimental.withTimeoutOrNull(duration.toNanos(), TimeUnit.NANOSECONDS, block)

/**
 * @suppress **Deprecated**: for binary compatibility only
 */
@Deprecated("for binary compatibility only", level=DeprecationLevel.HIDDEN)
public suspend fun <T> withTimeoutOrNull(duration: Duration, block: suspend () -> T): T? =
        kotlinx.coroutines.experimental.withTimeoutOrNull(duration.toNanos(), TimeUnit.NANOSECONDS) { block() }
