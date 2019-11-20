/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/**
 * Yields the thread (or thread pool) of the current coroutine dispatcher to other coroutines to run if possible.
 * 
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed when this suspending function is invoked or while
 * this function is waiting for dispatch, it resumes with a [CancellationException].
 *
 * **Note**: This function always [checks for cancellation][ensureActive] even when it does not suspend.
 *
 * ### Implementation details
 *
 * If the coroutine dispatcher is [Unconfined][Dispatchers.Unconfined], this
 * functions suspends only when there are other unconfined coroutines working and forming an event-loop.
 * For other dispatchers, this function does not call [CoroutineDispatcher.isDispatchNeeded] and
 * always suspends to be resumed later. If there is no [CoroutineDispatcher] in the context, it does not suspend.
 */
public suspend fun yield(): Unit = suspendCoroutineUninterceptedOrReturn sc@ { uCont ->
    val context = uCont.context
    context.checkCompletion()
    val cont = uCont.intercepted() as? DispatchedContinuation<Unit> ?: return@sc Unit
    // Special case for the unconfined dispatcher that can yield only in existing unconfined loop
    if (cont.dispatcher === Unconfined) return@sc if (cont.yieldUndispatched()) COROUTINE_SUSPENDED else Unit
    cont.dispatchYield(Unit)
    COROUTINE_SUSPENDED
}

internal fun CoroutineContext.checkCompletion() {
    val job = get(Job)
    if (job != null && !job.isActive) throw job.getCancellationException()
}
