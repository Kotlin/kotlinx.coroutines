package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.intrinsics.*

/**
 * Yields the thread (or thread pool) of the current coroutine dispatcher
 * to other coroutines on the same dispatcher to run if possible.
 *
 * This suspending function is cancellable: if the [Job] of the current coroutine is cancelled while
 * [yield] is invoked or while waiting for dispatch, it immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**: even if this function is ready to return the result, but was cancelled
 * while suspended, [CancellationException] will be thrown. See [suspendCancellableCoroutine] for low-level details.
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
    context.ensureActive()
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
