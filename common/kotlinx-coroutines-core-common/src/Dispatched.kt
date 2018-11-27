/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

@Suppress("PrivatePropertyName")
private val UNDEFINED = Symbol("UNDEFINED")

@NativeThreadLocal
internal object UndispatchedEventLoop {
    data class EventLoop(
        @JvmField var isActive: Boolean = false,
        @JvmField val queue: ArrayQueue<Runnable> = ArrayQueue()
    )

    @JvmField
    internal val threadLocalEventLoop = CommonThreadLocal { EventLoop() }

    /**
     * Executes given [block] as part of current event loop, updating related to block [continuation]
     * mode and state if continuation is not resumed immediately.
     * [doYield] indicates whether current continuation is yielding (to provide fast-path if event-loop is empty).
     * Returns `true` if execution of continuation was queued (trampolined) or `false` otherwise.
     */
    inline fun execute(continuation: DispatchedContinuation<*>, contState: Any?, mode: Int,
                       doYield: Boolean = false, block: () -> Unit) : Boolean {
        val eventLoop = threadLocalEventLoop.get()
        if (eventLoop.isActive) {
            // If we are yielding and queue is empty, we can bail out as part of fast path
            if (doYield && eventLoop.queue.isEmpty) {
                return false
            }

            continuation._state = contState
            continuation.resumeMode = mode
            eventLoop.queue.addLast(continuation)
            return true
        }

        runEventLoop(eventLoop, block)
        return false
    }

    fun resumeUndispatched(task: DispatchedTask<*>): Boolean {
        val eventLoop = threadLocalEventLoop.get()
        if (eventLoop.isActive) {
            eventLoop.queue.addLast(task)
            return true
        }

        runEventLoop(eventLoop, { task.resume(task.delegate, MODE_UNDISPATCHED) })
        return false
    }

    inline fun runEventLoop(eventLoop: EventLoop, block: () -> Unit) {
        try {
            eventLoop.isActive = true
            block()
            while (true) {
                val nextEvent = eventLoop.queue.removeFirstOrNull() ?: return
                nextEvent.run()
            }
        } catch (e: Throwable) {
            /*
             * This exception doesn't happen normally, only if user either submitted throwing runnable
             * or if we have a bug in implementation. Anyway, reset state of the dispatcher to the initial.
             */
            eventLoop.queue.clear()
            throw DispatchException("Unexpected exception in undispatched event loop, clearing pending tasks", e)
        } finally {
            eventLoop.isActive = false
        }
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
            UndispatchedEventLoop.execute(this, state, MODE_ATOMIC_DEFAULT) {
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
            UndispatchedEventLoop.execute(this, value, MODE_CANCELLABLE) {
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
            UndispatchedEventLoop.execute(this, state, MODE_CANCELLABLE) {
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
    @JvmField var resumeMode: Int
) : SchedulerTask() {
    public abstract val delegate: Continuation<T>

    public abstract fun takeState(): Any?

    @Suppress("UNCHECKED_CAST")
    public open fun <T> getSuccessfulResult(state: Any?): T =
        state as T

    public fun getExceptionalResult(state: Any?): Throwable? =
        (state as? CompletedExceptionally)?.cause

    public final override fun run() {
        val taskContext = this.taskContext
        try {
            val delegate = delegate as DispatchedContinuation<T>
            val continuation = delegate.continuation
            val context = continuation.context
            val job = if (resumeMode.isCancellableMode) context[Job] else null
            val state = takeState() // NOTE: Must take state in any case, even if cancelled
            withCoroutineContext(context, delegate.countOrElement) {
                if (job != null && !job.isActive)
                    continuation.resumeWithException(job.getCancellationException())
                else {
                    val exception = getExceptionalResult(state)
                    if (exception != null)
                        continuation.resumeWithStackTrace(exception)
                    else
                        continuation.resume(getSuccessfulResult(state))
                }
            }
        } catch (e: Throwable) {
            throw DispatchException("Unexpected exception running $this", e)
        } finally {
            taskContext.afterTask()
        }
    }
}

internal fun DispatchedContinuation<Unit>.yieldUndispatched(): Boolean =
    UndispatchedEventLoop.execute(this, Unit, MODE_CANCELLABLE, doYield = true) {
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
            UndispatchedEventLoop.resumeUndispatched(this)
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
