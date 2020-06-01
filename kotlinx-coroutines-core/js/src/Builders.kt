/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

@Suppress("NOTHING_TO_INLINE") // Save an entry on call stack
internal actual inline fun <T, R> startCoroutine(
    start: CoroutineStart,
    receiver: R,
    completion: Continuation<T>,
    noinline onCancellation: ((cause: Throwable) -> Unit)?,
    noinline block: suspend R.() -> T
) =
    startCoroutineImpl(start, receiver, completion, onCancellation, block)

@Suppress("NOTHING_TO_INLINE") // Save an entry on call stack
internal actual inline fun <T, R> startAbstractCoroutine(
    start: CoroutineStart,
    receiver: R,
    coroutine: AbstractCoroutine<T>,
    noinline block: suspend R.() -> T
) {
    startCoroutineImpl(start, receiver, coroutine, null, block)
}

@Suppress("NOTHING_TO_INLINE") // Save an entry on call stack
internal actual inline fun <T, R> saveLazyCoroutine(
    coroutine: AbstractCoroutine<T>,
    receiver: R,
    noinline block: suspend R.() -> T
): Any =
    block.createCoroutineUnintercepted(receiver, coroutine)

@Suppress("NOTHING_TO_INLINE", "UNCHECKED_CAST") // Save an entry on call stack
internal actual inline fun <T, R> startLazyCoroutine(
    saved: Any,
    coroutine: AbstractCoroutine<T>,
    receiver: R
) =
    (saved as Continuation<Unit>).startCoroutineCancellable(coroutine)
