package kotlinx.coroutines.intrinsics

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/**
 * Use this function to start a new coroutine in [CoroutineStart.UNDISPATCHED] mode &mdash;
 * immediately execute the coroutine in the current thread until the next suspension.
 * It does not use [ContinuationInterceptor], but updates the context of the current thread for the new coroutine.
 */
internal fun <R, T> (suspend (R) -> T).startCoroutineUndispatched(receiver: R, completion: Continuation<T>) {
    val actualCompletion = probeCoroutineCreated(completion)
    val value = try {
        /* The code below is started immediately in the current stack-frame
         * and runs until the first suspension point. */
        withCoroutineContext(actualCompletion.context, null) {
            probeCoroutineResumed(actualCompletion)
            startCoroutineUninterceptedOrReturn(receiver, actualCompletion)
        }
    } catch (e: Throwable) {
        val reportException = if (e is DispatchException) e.cause else e
        actualCompletion.resumeWithException(reportException)
        return
    }
    if (value !== COROUTINE_SUSPENDED) {
        @Suppress("UNCHECKED_CAST")
        actualCompletion.resume(value as T)
    }
}

/**
 * Starts this coroutine with the given code [block] in the same context and returns the coroutine result when it
 * completes without suspension.
 * This function shall be invoked at most once on this coroutine.
 * This function checks cancellation of the outer [Job] on fast-path.
 *
 * It starts the coroutine using [startCoroutineUninterceptedOrReturn].
 */
internal fun <T, R> ScopeCoroutine<T>.startUndispatchedOrReturn(
    receiver: R, block: suspend R.() -> T
): Any? = startUndspatched(alwaysRethrow = true, receiver, block)

/**
 * Same as [startUndispatchedOrReturn], but ignores [TimeoutCancellationException] on fast-path.
 */
internal fun <T, R> ScopeCoroutine<T>.startUndispatchedOrReturnIgnoreTimeout(
    receiver: R, block: suspend R.() -> T
): Any? = startUndspatched(alwaysRethrow = false, receiver, block)

/**
 * Starts and handles the result of an undispatched coroutine, potentially with children.
 * For example, it handles `coroutineScope { ...suspend of throw, maybe start children... }`
 * and `launch(start = UNDISPATCHED) { ... }`
 *
 * @param alwaysRethrow specifies whether an exception should be unconditioanlly rethrown.
 *     It is a tweak for 'withTimeout' in order to successfully return values when the block was cancelled:
 *     i.e. `withTimeout(1ms) { Thread.sleep(1000); 42 }` should not fail.
 */
private fun <T, R> ScopeCoroutine<T>.startUndspatched(
    alwaysRethrow: Boolean,
    receiver: R, block: suspend R.() -> T
): Any? {
    val result = try {
        block.startCoroutineUninterceptedOrReturn(receiver, this)
    } catch (e: DispatchException) {
        // Special codepath for failing CoroutineDispatcher: rethrow an exception
        // immediately without waiting for children to indicate something is wrong
        dispatchExceptionAndMakeCompleting(e)
    } catch (e: Throwable) {
        CompletedExceptionally(e)
    }

    /*
     * We are trying to complete our undispatched block with the following possible codepaths:
     * 1) The coroutine just suspended. I.e. `coroutineScope { .. suspend here }`.
     *   Then just suspend
     * 2) The coroutine completed with something, but has active children. Wait for them, also suspend
     * 3) The coroutine succesfully completed. Return or rethrow its result.
     */
    if (result === COROUTINE_SUSPENDED) return COROUTINE_SUSPENDED // (1)
    val state = makeCompletingOnce(result)
    if (state === COMPLETING_WAITING_CHILDREN) return COROUTINE_SUSPENDED // (2)
    afterCompletionUndispatched()
    return if (state is CompletedExceptionally) { // (3)
        when {
            alwaysRethrow || notOwnTimeout(state.cause) -> throw recoverStackTrace(state.cause, uCont)
            result is CompletedExceptionally -> throw recoverStackTrace(result.cause, uCont)
            else -> result
        }
    } else {
        state.unboxState()
    }
}

private fun ScopeCoroutine<*>.notOwnTimeout(cause: Throwable): Boolean {
    return cause !is TimeoutCancellationException || cause.coroutine !== this
}

private fun ScopeCoroutine<*>.dispatchExceptionAndMakeCompleting(e: DispatchException): Nothing {
    makeCompleting(CompletedExceptionally(e.cause))
    throw recoverStackTrace(e.cause, uCont)
}
