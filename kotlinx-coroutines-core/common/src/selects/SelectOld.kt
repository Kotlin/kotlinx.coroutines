/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/*
 * For binary compatibility, we need to maintain the previous `select` implementations.
 * Thus, we keep [SelectBuilderImpl] and [UnbiasedSelectBuilderImpl] and implement the
 * functions marked with `@PublishedApi`.
 *
 * We keep the old `select` functions as [selectOld] and [selectUnbiasedOld] for test purpose.
 */

@PublishedApi
internal class SelectBuilderImpl<R>(
    uCont: Continuation<R> // unintercepted delegate continuation
) : SelectImplementation<R>(uCont.context) {
    private val cont = CancellableContinuationImpl(uCont.intercepted(), MODE_CANCELLABLE)

    @PublishedApi
    internal fun getResult(): Any? {
        // In the current `select` design, the [select] and [selectUnbiased] functions
        // do not wrap the operation in `suspendCoroutineUninterceptedOrReturn` and
        // suspend explicitly via [doSelect] call, which returns the final result.
        // However, [doSelect] is a suspend function, so it cannot be invoked directly.
        // In addition, the `select` builder is eligible to throw an exception, which
        // should be handled properly.
        //
        // As a solution, we:
        // 1) check whether the `select` building is already completed with exception, finishing immediately in this case;
        // 2) create a CancellableContinuationImpl with the provided unintercepted continuation as a delegate;
        // 3) wrap the [doSelect] call in an additional coroutine, which we launch in UNDISPATCHED mode;
        // 4) resume the created CancellableContinuationImpl after the [doSelect] invocation completes;
        // 5) use CancellableContinuationImpl.getResult() as a result of this function.
        if (cont.isCompleted) return cont.getResult()
        CoroutineScope(context).launch(start = CoroutineStart.UNDISPATCHED) {
            val result = try {
                doSelect()
            } catch (e: Throwable) {
                cont.resumeUndispatchedWithException(e)
                return@launch
            }
            cont.resumeUndispatched(result)
        }
        return cont.getResult()
    }

    @PublishedApi
    internal fun handleBuilderException(e: Throwable) {
        cont.resumeWithException(e) // will be thrown later via `cont.getResult()`
    }
}

@PublishedApi
internal class UnbiasedSelectBuilderImpl<R>(
    uCont: Continuation<R> // unintercepted delegate continuation
) : UnbiasedSelectImplementation<R>(uCont.context) {
    private val cont = CancellableContinuationImpl(uCont.intercepted(), MODE_CANCELLABLE)

    @PublishedApi
    internal fun initSelectResult(): Any? {
        // Here, we do the same trick as in [SelectBuilderImpl].
        if (cont.isCompleted) return cont.getResult()
        CoroutineScope(context).launch(start = CoroutineStart.UNDISPATCHED) {
            val result = try {
                doSelect()
            } catch (e: Throwable) {
                cont.resumeUndispatchedWithException(e)
                return@launch
            }
            cont.resumeUndispatched(result)
        }
        return cont.getResult()
    }

    @PublishedApi
    internal fun handleBuilderException(e: Throwable) {
        cont.resumeWithException(e)
    }
}

/*
 * This is the old version of `select`. It should work to guarantee binary compatibility.
 *
 * Internal note:
 * We do test it manually by changing the implementation of **new** select with the following:
 * ```
 * public suspend inline fun <R> select(crossinline builder: SelectBuilder<R>.() -> Unit): R {
 *     contract {
 *         callsInPlace(builder, InvocationKind.EXACTLY_ONCE)
 *     }
 *     return selectOld(builder)
 * }
 * ```
 *
 * These signatures are not used by the already compiled code, but their body is.
 */
@PublishedApi
internal suspend inline fun <R> selectOld(crossinline builder: SelectBuilder<R>.() -> Unit): R {
    return suspendCoroutineUninterceptedOrReturn { uCont ->
        val scope = SelectBuilderImpl(uCont)
        try {
            builder(scope)
        } catch (e: Throwable) {
            scope.handleBuilderException(e)
        }
        scope.getResult()
    }
}

// This is the old version of `selectUnbiased`. It should work to guarantee binary compatibility.
@PublishedApi
internal suspend inline fun <R> selectUnbiasedOld(crossinline builder: SelectBuilder<R>.() -> Unit): R =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        val scope = UnbiasedSelectBuilderImpl(uCont)
        try {
            builder(scope)
        } catch (e: Throwable) {
            scope.handleBuilderException(e)
        }
        scope.initSelectResult()
    }

@OptIn(ExperimentalStdlibApi::class)
private fun <T> CancellableContinuation<T>.resumeUndispatched(result: T) {
    val dispatcher = context[CoroutineDispatcher]
    if (dispatcher != null) {
        dispatcher.resumeUndispatched(result)
    } else {
        resume(result)
    }
}

@OptIn(ExperimentalStdlibApi::class)
private fun CancellableContinuation<*>.resumeUndispatchedWithException(exception: Throwable) {
    val dispatcher = context[CoroutineDispatcher]
    if (dispatcher != null) {
        dispatcher.resumeUndispatchedWithException(exception)
    } else {
        resumeWithException(exception)
    }
}
