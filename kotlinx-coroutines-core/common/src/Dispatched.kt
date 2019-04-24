/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

@Suppress("PrivatePropertyName")
@SharedImmutable
private val UNDEFINED = Symbol("UNDEFINED")

/**
 * Executes given [block] as part of current event loop, updating current continuation
 * mode and state if continuation is not resumed immediately.
 * [doYield] indicates whether current continuation is yielding (to provide fast-path if event-loop is empty).
 * Returns `true` if execution of continuation was queued (trampolined) or `false` otherwise.
 */
private inline fun DispatchedContinuation<*>.executeUnconfined(
    contState: Any?, mode: Int, doYield: Boolean = false,
    block: () -> Unit
) : Boolean {
    val eventLoop = ThreadLocalEventLoop.eventLoop
    // If we are yielding and unconfined queue is empty, we can bail out as part of fast path
    if (doYield && eventLoop.isUnconfinedQueueEmpty) return false
    return if (eventLoop.isUnconfinedLoopActive) {
        // When unconfined loop is active -- dispatch continuation for execution to avoid stack overflow
        _state = contState
        resumeMode = mode
        eventLoop.dispatchUnconfined(this)
        true // queued into the active loop
    } else {
        // Was not active -- run event loop until all unconfined tasks are executed
        runUnconfinedEventLoop(eventLoop, block = block)
        false
    }
}

private fun DispatchedTask<*>.resumeUnconfined() {
    val eventLoop = ThreadLocalEventLoop.eventLoop
    if (eventLoop.isUnconfinedLoopActive) {
        // When unconfined loop is active -- dispatch continuation for execution to avoid stack overflow
        eventLoop.dispatchUnconfined(this)
    } else {
        // Was not active -- run event loop until all unconfined tasks are executed
        runUnconfinedEventLoop(eventLoop) {
            resume(delegate, MODE_UNDISPATCHED)
        }
    }
}

private inline fun DispatchedTask<*>.runUnconfinedEventLoop(
    eventLoop: EventLoop,
    block: () -> Unit
) {
    eventLoop.incrementUseCount(unconfined = true)
    try {
        block()
        while (true) {
            // break when all unconfined continuations where executed
            if (!eventLoop.processUnconfinedEvent()) break
        }
    } catch (e: Throwable) {
        /*
         * This exception doesn't happen normally, only if we have a bug in implementation.
         * Report it as a fatal exception.
         */
        handleFatalException(e, null)
    } finally {
        eventLoop.decrementUseCount(unconfined = true)
    }
}

internal class DispatchedContinuation<in T>(
    @JvmField val dispatcher: CoroutineDispatcher,
    @JvmField val continuation: Continuation<T>
) : DispatchedTask<T>(MODE_ATOMIC_DEFAULT), CoroutineStackFrame, Continuation<T> by continuation {
    @JvmField
    @Suppress("PropertyName")
    internal var _state: Any? = UNDEFINED
    override val callerFrame: CoroutineStackFrame? = continuation as? CoroutineStackFrame
    override fun getStackTraceElement(): StackTraceElement? = null
    @JvmField // pre-cached value to avoid ctx.fold on every resumption
    internal val countOrElement = threadContextElements(context)

    override fun takeState(): Any? {
        val state = _state
        check(state !== UNDEFINED) // fail-fast if repeatedly invoked
        _state = UNDEFINED
        return state
    }

    override val delegate: Continuation<T>
        get() = this

    override fun resumeWith(result: Result<T>) {
        val context = continuation.context
        val state = result.toState()
        if (dispatcher.isDispatchNeeded(context)) {
            _state = state
            resumeMode = MODE_ATOMIC_DEFAULT
            dispatcher.dispatch(context, this)
        } else {
            executeUnconfined(state, MODE_ATOMIC_DEFAULT) {
                withCoroutineContext(this.context, countOrElement) {
                    continuation.resumeWith(result)
                }
            }
        }
    }

    @Suppress("NOTHING_TO_INLINE") // we need it inline to save us an entry on the stack
    inline fun resumeCancellable(value: T) {
        if (dispatcher.isDispatchNeeded(context)) {
            _state = value
            resumeMode = MODE_CANCELLABLE
            dispatcher.dispatch(context, this)
        } else {
            executeUnconfined(value, MODE_CANCELLABLE) {
                if (!resumeCancelled()) {
                    resumeUndispatched(value)
                }
            }
        }
    }

    @Suppress("NOTHING_TO_INLINE") // we need it inline to save us an entry on the stack
    inline fun resumeCancellableWithException(exception: Throwable) {
        val context = continuation.context
        val state = CompletedExceptionally(exception)
        if (dispatcher.isDispatchNeeded(context)) {
            _state = CompletedExceptionally(exception)
            resumeMode = MODE_CANCELLABLE
            dispatcher.dispatch(context, this)
        } else {
            executeUnconfined(state, MODE_CANCELLABLE) {
                if (!resumeCancelled()) {
                    resumeUndispatchedWithException(exception)
                }
            }
        }
    }

    @Suppress("NOTHING_TO_INLINE")
    inline fun resumeCancelled(): Boolean {
        val job = context[Job]
        if (job != null && !job.isActive) {
            resumeWithException(job.getCancellationException())
            return true
        }

        return false
    }

    @Suppress("NOTHING_TO_INLINE") // we need it inline to save us an entry on the stack
    inline fun resumeUndispatched(value: T) {
        withCoroutineContext(context, countOrElement) {
            continuation.resume(value)
        }
    }

    @Suppress("NOTHING_TO_INLINE") // we need it inline to save us an entry on the stack
    inline fun resumeUndispatchedWithException(exception: Throwable) {
        withCoroutineContext(context, countOrElement) {
            continuation.resumeWithStackTrace(exception)
        }
    }

    // used by "yield" implementation
    internal fun dispatchYield(value: T) {
        val context = continuation.context
        _state = value
        resumeMode = MODE_CANCELLABLE
        dispatcher.dispatchYield(context, this)
    }

    override fun toString(): String =
        "DispatchedContinuation[$dispatcher, ${continuation.toDebugString()}]"
}

internal fun <T> Continuation<T>.resumeCancellable(value: T) = when (this) {
    is DispatchedContinuation -> resumeCancellable(value)
    else -> resume(value)
}

internal fun <T> Continuation<T>.resumeCancellableWithException(exception: Throwable) = when (this) {
    is DispatchedContinuation -> resumeCancellableWithException(exception)
    else -> resumeWithStackTrace(exception)
}

internal fun <T> Continuation<T>.resumeDirect(value: T) = when (this) {
    is DispatchedContinuation -> continuation.resume(value)
    else -> resume(value)
}

internal fun <T> Continuation<T>.resumeDirectWithException(exception: Throwable) = when (this) {
    is DispatchedContinuation -> continuation.resumeWithStackTrace(exception)
    else -> resumeWithStackTrace(exception)
}

internal abstract class DispatchedTask<in T>(
    @JvmField public var resumeMode: Int
) : SchedulerTask() {
    internal abstract val delegate: Continuation<T>

    internal abstract fun takeState(): Any?

    internal open fun cancelResult(state: Any?, cause: Throwable) {}

    @Suppress("UNCHECKED_CAST")
    internal open fun <T> getSuccessfulResult(state: Any?): T =
        state as T

    internal fun getExceptionalResult(state: Any?): Throwable? =
        (state as? CompletedExceptionally)?.cause

    public final override fun run() {
        val taskContext = this.taskContext
        var exception: Throwable? = null
        try {
            val delegate = delegate as DispatchedContinuation<T>
            val continuation = delegate.continuation
            val context = continuation.context
            val job = if (resumeMode.isCancellableMode) context[Job] else null
            val state = takeState() // NOTE: Must take state in any case, even if cancelled
            withCoroutineContext(context, delegate.countOrElement) {
                if (job != null && !job.isActive) {
                    val cause = job.getCancellationException()
                    cancelResult(state, cause)
                    continuation.resumeWithStackTrace(cause)
                } else {
                    val exception = getExceptionalResult(state)
                    if (exception != null)
                        continuation.resumeWithStackTrace(exception)
                    else
                        continuation.resume(getSuccessfulResult(state))
                }
            }
        } catch (e: Throwable) {
            // This instead of runCatching to have nicer stacktrace and debug experience
            exception = e
        } finally {
            val result = runCatching { taskContext.afterTask() }
            handleFatalException(exception, result.exceptionOrNull())
        }
    }

    /**
     * Machinery that handles fatal exceptions in kotlinx.coroutines.
     * There are two kinds of fatal exceptions:
     *
     * 1) Exceptions from kotlinx.coroutines code. Such exceptions indicate that either
     *    the library or the compiler has a bug that breaks internal invariants.
     *    They usually have specific workarounds, but require careful study of the cause and should
     *    be reported to the maintainers and fixed on the library's side anyway.
     *
     * 2) Exceptions from [ThreadContextElement.updateThreadContext] and [ThreadContextElement.restoreThreadContext].
     *    While a user code can trigger such exception by providing an improper implementation of [ThreadContextElement],
     *    we can't ignore it because it may leave coroutine in the inconsistent state.
     *    If you encounter such exception, you can either disable this context element or wrap it into
     *    another context element that catches all exceptions and handles it in the application specific manner.
     *
     * Fatal exception handling can be intercepted with [CoroutineExceptionHandler] element in the context of
     * a failed coroutine, but such exceptions should be reported anyway.
     */
    internal fun handleFatalException(exception: Throwable?, finallyException: Throwable?) {
        if (exception === null && finallyException === null) return
        if (exception !== null && finallyException !== null) {
            exception.addSuppressedThrowable(finallyException)
        }

        val cause = exception ?: finallyException
        val reason = CoroutinesInternalError("Fatal exception in coroutines machinery for $this. " +
                "Please read KDoc to 'handleFatalException' method and report this incident to maintainers", cause!!)
        handleCoroutineException(this.delegate.context, reason)
    }
}

internal fun DispatchedContinuation<Unit>.yieldUndispatched(): Boolean =
    executeUnconfined(Unit, MODE_CANCELLABLE, doYield = true) {
        run()
    }

internal fun <T> DispatchedTask<T>.dispatch(mode: Int = MODE_CANCELLABLE) {
    val delegate = this.delegate
    if (mode.isDispatchedMode && delegate is DispatchedContinuation<*> && mode.isCancellableMode == resumeMode.isCancellableMode) {
        // dispatch directly using this instance's Runnable implementation
        val dispatcher = delegate.dispatcher
        val context = delegate.context
        if (dispatcher.isDispatchNeeded(context)) {
            dispatcher.dispatch(context, this)
        } else {
            resumeUnconfined()
        }
    } else {
        resume(delegate, mode)
    }
}

internal fun <T> DispatchedTask<T>.resume(delegate: Continuation<T>, useMode: Int) {
    // slow-path - use delegate
    val state = takeState()
    val exception = getExceptionalResult(state)
    if (exception != null) {
        delegate.resumeWithExceptionMode(exception, useMode)
    } else {
        delegate.resumeMode(getSuccessfulResult(state), useMode)
    }
}


@Suppress("NOTHING_TO_INLINE")
internal inline fun Continuation<*>.resumeWithStackTrace(exception: Throwable) {
    resumeWith(Result.failure(recoverStackTrace(exception, this)))
}
