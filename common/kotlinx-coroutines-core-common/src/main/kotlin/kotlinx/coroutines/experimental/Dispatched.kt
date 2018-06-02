/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.internal.*
import kotlinx.coroutines.experimental.internalAnnotations.*
import kotlin.coroutines.experimental.*

@Suppress("PrivatePropertyName")
private val UNDEFINED = Symbol("UNDEFINED")

internal class DispatchedContinuation<in T>(
    @JvmField val dispatcher: CoroutineDispatcher,
    @JvmField val continuation: Continuation<T>
) : Continuation<T> by continuation, DispatchedTask<T> {
    private var _state: Any? = UNDEFINED
    public override var resumeMode: Int = 0

    override fun takeState(): Any? {
        val state = _state
        check(state !== UNDEFINED) // fail-fast if repeatedly invoked
        _state = UNDEFINED
        return state
    }

    override val delegate: Continuation<T>
        get() = this

    override fun resume(value: T) {
        val context = continuation.context
        if (dispatcher.isDispatchNeeded(context)) {
            _state = value
            resumeMode = MODE_ATOMIC_DEFAULT
            dispatcher.dispatch(context, this)
        } else
            resumeUndispatched(value)
    }

    override fun resumeWithException(exception: Throwable) {
        val context = continuation.context
        if (dispatcher.isDispatchNeeded(context)) {
            _state = CompletedExceptionally(exception)
            resumeMode = MODE_ATOMIC_DEFAULT
            dispatcher.dispatch(context, this)
        } else
            resumeUndispatchedWithException(exception)
    }

    @Suppress("NOTHING_TO_INLINE") // we need it inline to save us an entry on the stack
    inline fun resumeCancellable(value: T) {
        val context = continuation.context
        if (dispatcher.isDispatchNeeded(context)) {
            _state = value
            resumeMode = MODE_CANCELLABLE
            dispatcher.dispatch(context, this)
        } else
            resumeUndispatched(value)
    }

    @Suppress("NOTHING_TO_INLINE") // we need it inline to save us an entry on the stack
    inline fun resumeCancellableWithException(exception: Throwable) {
        val context = continuation.context
        if (dispatcher.isDispatchNeeded(context)) {
            _state = CompletedExceptionally(exception)
            resumeMode = MODE_CANCELLABLE
            dispatcher.dispatch(context, this)
        } else
            resumeUndispatchedWithException(exception)
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
        dispatcher.dispatch(context, this)
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

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
public interface DispatchedTask<in T> : Runnable {
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

/**
 * @suppress **This is unstable API and it is subject to change.**
 */
public fun <T> DispatchedTask<T>.dispatch(mode: Int = MODE_CANCELLABLE) {
    var useMode = mode
    val delegate = this.delegate
    if (mode.isDispatchedMode && delegate is DispatchedContinuation<*> && mode.isCancellableMode == resumeMode.isCancellableMode) {
        // dispatch directly using this instance's Runnable implementation
        val dispatcher = delegate.dispatcher
        val context = delegate.context
        if (dispatcher.isDispatchNeeded(context)) {
            dispatcher.dispatch(context, this)
            return // and that's it -- dispatched via fast-path
        } else {
            useMode = MODE_UNDISPATCHED
        }
    }
    // slow-path - use delegate
    val state = takeState()
    val exception = getExceptionalResult(state)
    if (exception != null) {
        delegate.resumeWithExceptionMode(exception, useMode)
    } else {
        delegate.resumeMode(getSuccessfulResult(state), useMode)
    }
}
