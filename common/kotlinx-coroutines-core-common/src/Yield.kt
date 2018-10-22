/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/**
 * Yields a thread (or thread pool) of the current coroutine dispatcher to other coroutines to run.
 * If the coroutine dispatcher does not have its own thread pool (like [Dispatchers.Unconfined]) then this
 * function does nothing, but checks if the coroutine [Job] was completed.
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed when this suspending function is invoked or while
 * this function is waiting for dispatching, it resumes with [CancellationException].
 */
public suspend fun yield(): Unit = suspendCoroutineUninterceptedOrReturn sc@ { uCont ->
    val context = uCont.context
    context.checkCompletion()
    val cont = uCont.intercepted() as? DispatchedContinuation<Unit> ?: return@sc Unit
    if (!cont.dispatcher.isDispatchNeeded(context)) {
        return@sc if (cont.yield()) COROUTINE_SUSPENDED else Unit
    }
    cont.dispatchYield(Unit)
    COROUTINE_SUSPENDED
}

internal fun CoroutineContext.checkCompletion() {
    val job = get(Job)
    if (job != null && !job.isActive) throw job.getCancellationException()
}
