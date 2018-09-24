/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.selects.*
import kotlinx.coroutines.experimental.timeunit.*

@Deprecated(level = DeprecationLevel.HIDDEN, message = "binary compatibility")
public suspend fun <T> withTimeout(time: Int, block: suspend CoroutineScope.() -> T): T =
    withTimeout(time.toLong(), block)

/**
 * Runs a given suspending [block] of code inside a coroutine with a specified timeout and throws
 * [TimeoutCancellationException] if timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and the active or next invocation of
 * cancellable suspending function inside the block throws [TimeoutCancellationException].
 * Even if the code in the block suppresses [TimeoutCancellationException], it
 * is still thrown by `withTimeout` invocation.
 *
 * The sibling function that does not throw exception on timeout is [withTimeoutOrNull].
 * Note, that timeout action can be specified for [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * This function delegates to [Delay.invokeOnTimeout] if the context [CoroutineDispatcher]
 * implements [Delay] interface, otherwise it tracks time using a built-in single-threaded scheduled executor service.
 *
 * @param time timeout time
 * @param unit timeout unit (milliseconds by default)
 *
 * @suppress **Deprecated**: Replace with `withTimeout(unit.toMillis(time), block)`
 */
// todo: review usage in Guides and samples
@Deprecated(
    message = "Replace with withTimeout(unit.toMillis(time), block)",
    replaceWith = ReplaceWith("withTimeout(unit.toMillis(time), block)")
)
public suspend fun <T> withTimeout(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS, block: suspend CoroutineScope.() -> T): T =
    withTimeout(time.convertToMillis(unit), block)

@Deprecated(level = DeprecationLevel.HIDDEN, message = "binary compatibility")
public suspend fun <T> withTimeoutOrNull(time: Int, block: suspend CoroutineScope.() -> T): T? =
    withTimeoutOrNull(time.toLong(), TimeUnit.MILLISECONDS, block)

/**
 * Runs a given suspending block of code inside a coroutine with a specified timeout and returns
 * `null` if this timeout was exceeded.
 *
 * The code that is executing inside the [block] is cancelled on timeout and the active or next invocation of
 * cancellable suspending function inside the block throws [TimeoutCancellationException].
 * **NB**: this method is exception-unsafe. Even if the code in the block suppresses [TimeoutCancellationException], this
 * invocation of `withTimeoutOrNull` still returns `null` and thrown exception will be ignored.
 *
 * The sibling function that throws exception on timeout is [withTimeout].
 * Note, that timeout action can be specified for [select] invocation with [onTimeout][SelectBuilder.onTimeout] clause.
 *
 * This function delegates to [Delay.invokeOnTimeout] if the context [CoroutineDispatcher]
 * implements [Delay] interface, otherwise it tracks time using a built-in single-threaded scheduled executor service.
 *
 * @param time timeout time
 * @param unit timeout unit (milliseconds by default)
 * @suppress **Deprecated**: Replace with `withTimeoutOrNull(unit.toMillis(time), block)`
 */
// todo: review usage in Guides and samples
@Deprecated(
    message = "Replace with withTimeoutOrNull(unit.toMillis(time), block)",
    replaceWith = ReplaceWith("withTimeoutOrNull(unit.toMillis(time), block)")
)
public suspend fun <T> withTimeoutOrNull(time: Long, unit: TimeUnit = TimeUnit.MILLISECONDS, block: suspend CoroutineScope.() -> T): T? =
    withTimeoutOrNull(time.convertToMillis(unit), block)

