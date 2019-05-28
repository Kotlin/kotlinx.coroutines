/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/**
 * Creates a [CoroutineScope] and calls the specified suspend block with this scope.
 * This builder is similar to [coroutineScope] with the only exception that it *ties* lifecycle of children
 * and itself regarding the cancellation, thus being cancelled when one of the children becomes cancelled.
 *
 * For example:
 * ```
 * flowScope {
 *     launch {
 *         throw CancellationException()
 *     }
 * } // <- CE will be rethrown here
 * ```
 */
internal suspend fun <R> flowScope(block: suspend CoroutineScope.() -> R): R =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        val coroutine = FlowScope(uCont.context, uCont)
        coroutine.startUndispatchedOrReturn(coroutine, block)
    }

private class FlowScope<T>(context: CoroutineContext, uCont: Continuation<T>) : ScopeCoroutine<T>(context, uCont) {
    public override fun cancelOnChildCancellation(cause: CancellationException) = cause !is ChildCancelledException
}

internal class ChildCancelledException : CancellationException(null)
