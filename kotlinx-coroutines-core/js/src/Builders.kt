/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun <T, R> startAbstractCoroutine(
    start: CoroutineStart,
    receiver: R,
    coroutine: AbstractCoroutine<T>,
    noinline block: suspend R.() -> T
) = startCoroutineImpl(start, receiver, coroutine, null, block)