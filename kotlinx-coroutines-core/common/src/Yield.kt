/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
 * For other dispatchers, this function calls [CoroutineDispatcher.dispatch] and
 * always suspends to be resumed later regardless of the result of [CoroutineDispatcher.isDispatchNeeded].
 * If there is no [CoroutineDispatcher] in the context, it does not suspend.
 */
public suspend fun yield(): Unit = suspendCoroutineUninterceptedOrReturn sc@ { uCont ->
    val context = uCont.context
    context.checkCompletion()
    val cont = uCont.intercepted() as? DispatchedContinuation<Unit> ?: return@sc Unit
    if (cont.dispatcher.isDispatchNeeded(context)) {
        // this is a regular dispatcher -- do simple dispatchYield
        cont.dispatchYield(context, Unit)
    } else {
        // This is either an "immediate" dispatcher or the Unconfined dispatcher
        // This code detects the Unconfined dispatcher even if it was wrapped into another dispatcher
        val yieldContext = YieldContext()
        cont.dispatchYield(context + yieldContext, Unit)
        // Special case for the unconfined dispatcher that can yield only in existing unconfined loop
        if (yieldContext.dispatcherWasUnconfined) {
            // Means that the Unconfined dispatcher got the call, but did not do anything.
            // See also code of "Unconfined.dispatch" function.
            return@sc if (cont.yieldUndispatched()) COROUTINE_SUSPENDED else Unit
        }
        // Otherwise, it was some other dispatcher that successfully dispatched the coroutine
    }
    COROUTINE_SUSPENDED
}

internal fun CoroutineContext.checkCompletion() {
    val job = get(Job)
    if (job != null && !job.isActive) throw job.getCancellationException()
}
