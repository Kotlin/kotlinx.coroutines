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
    data class State(
        @JvmField var isActive: Boolean = false,
        @JvmField val threadLocalQueue: ArrayQueue<Runnable> = ArrayQueue()
    )

    @JvmField
    internal val state = CommonThreadLocal { State() }

    inline fun execute(continuation: DispatchedContinuation<*>, contState: Any?, mode: Int, block: () -> Unit) {
        val state = state.get()
        if (state.isActive) {
            continuation._state = contState
            continuation.resumeMode = mode
            state.threadLocalQueue.addLast(continuation)
            return
        }

        runLoop(state, block)
    }

    fun resumeUndispatched(task: DispatchedTask<*>) {
        val state = state.get()
        if (state.isActive) {
            state.threadLocalQueue.addLast(task)
            return
        }

        runLoop(state, { task.resume(task.delegate, MODE_UNDISPATCHED) })
    }

    inline fun runLoop(state: State, block: () -> Unit) {
        try {
            state.isActive = true
            block()
            while (!state.threadLocalQueue.isEmpty) {
                val element = state.threadLocalQueue.removeFirst()
                element.run()
            }
        } catch (e: Throwable) {
            /*
             * This exception doesn't happen normally, only if user either submitted throwing runnable
             * or if we have a bug in implementation. Anyway, reset state of the dispatcher to the initial.
             */
            state.threadLocalQueue.clear()
            throw DispatchException("Unexpected exception in undispatched event loop, clearing pending tasks", e)
        } finally {
            state.isActive = false
        }
    }
}

internal class DispatchedContinuation<in T>(
    @JvmField val dispatcher: CoroutineDispatcher,
    @JvmField val continuation: Continuation<T>
) : Continuation<T> by continuation, DispatchedTask<T> {
    @JvmField
    @Suppress("PropertyName")
    internal var _state: Any? = UNDEFINED
    public override var resumeMode: Int = 0

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
                withCoroutineContext(this.context) {
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
        withCoroutineContext(context) {
            continuation.resume(value)
        }
    }

    @Suppress("NOTHING_TO_INLINE") // we need it inline to save us an entry on the stack
    inline fun resumeUndispatchedWithException(exception: Throwable) {
        withCoroutineContext(context) {
            continuation.resumeWithException(exception)
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
    else -> resumeWithException(exception)
}

internal fun <T> Continuation<T>.resumeDirect(value: T) = when (this) {
    is DispatchedContinuation -> continuation.resume(value)
    else -> resume(value)
}

internal fun <T> Continuation<T>.resumeDirectWithException(exception: Throwable) = when (this) {
    is DispatchedContinuation -> continuation.resumeWithException(exception)
    else -> resumeWithException(exception)
}

internal interface DispatchedTask<in T> : Runnable {
    public val delegate: Continuation<T>
    public val resumeMode: Int get() = MODE_CANCELLABLE

    public fun takeState(): Any?

    @Suppress("UNCHECKED_CAST")
    public fun <T> getSuccessfulResult(state: Any?): T =
        state as T

    public fun getExceptionalResult(state: Any?): Throwable? =
        (state as? CompletedExceptionally)?.cause

    public override fun run() {
        try {
            val delegate = delegate as DispatchedContinuation<T>
            val continuation = delegate.continuation
            val context = continuation.context
            val job = if (resumeMode.isCancellableMode) context[Job] else null
            val state = takeState() // NOTE: Must take state in any case, even if cancelled
            withCoroutineContext(context) {
                if (job != null && !job.isActive)
                    continuation.resumeWithException(job.getCancellationException())
                else {
                    val exception = getExceptionalResult(state)
                    if (exception != null)
                        continuation.resumeWithException(exception)
                    else
                        continuation.resume(getSuccessfulResult(state))
                }
            }
        } catch (e: Throwable) {
            throw DispatchException("Unexpected exception running $this", e)
        }
    }
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
