/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("DEPRECATION_ERROR")

package kotlinx.coroutines

import kotlinx.coroutines.CoroutineStart.*
import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * Abstract base class for implementation of coroutines in coroutine builders.
 *
 * This class implements completion [Continuation], [Job], and [CoroutineScope] interfaces.
 * It stores the result of continuation in the state of the job.
 * This coroutine waits for children coroutines to finish before completing and
 * fails through an intermediate _failing_ state.
 *
 * The following methods are available for override:
 *
 * * [onStart] is invoked when coroutine was created in not active state and is being [started][Job.start].
 * * [onCancelling] is invoked as soon as coroutine is being cancelled for any reason (or completes).
 * * [onCompleted] is invoked when coroutine completes with a value.
 * * [onCancelled] in invoked when coroutines completes with exception (cancelled).
 *
 * @param parentContext context of the parent coroutine.
 * @param active when `true` (by default) coroutine is created in _active_ state, when `false` in _new_ state.
 *               See [Job] for details.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public abstract class AbstractCoroutine<in T>(
    /**
     * Context of the parent coroutine.
     */
    @JvmField
    protected val parentContext: CoroutineContext,
    active: Boolean = true
) : JobSupport(active), Job, Continuation<T>, CoroutineScope {
    /**
     * Context of this coroutine that includes this coroutine as a [Job].
     */
    @Suppress("LeakingThis")
    public final override val context: CoroutineContext = parentContext + this

    /**
     * Context of this scope which is the same as the [context] of this coroutine.
     */
    public override val coroutineContext: CoroutineContext get() = context

    override val isActive: Boolean get() = super.isActive

    /**
     * Initializes parent job from the `parentContext` of this coroutine that was passed to it during construction.
     * It shall be invoked at most once after construction after all other initialization.
     * 
     * Invocation of this function may cause this coroutine to become cancelled if parent is already cancelled,
     * in which case it synchronously invokes all the corresponding handlers.
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal fun initParentJob() {
        initParentJobInternal(parentContext[Job])
    }

    /**
     * This function is invoked once when non-active coroutine (constructed with `active` set to `false)
     * is [started][start].
     */
    protected open fun onStart() {}

    internal final override fun onStartInternal() {
        onStart()
    }

    /**
     * This function is invoked once when job was completed normally with the specified [value],
     * right before all the waiters for coroutine's completion are notified.
     */
    protected open fun onCompleted(value: T) {}

    /**
     * This function is invoked once when job was cancelled with the specified [cause],
     * right before all the waiters for coroutine's completion are notified.
     *
     * **Note:** the state of the coroutine might not be final yet in this function and should not be queried.
     * You can use [completionCause] and [completionCauseHandled] to recover parameters that we passed
     * to this `onCancelled` invocation only when [isCompleted] returns `true`.
     *
     * @param cause The cancellation (failure) cause
     * @param handled `true` if the exception was handled by parent (always `true` when it is a [CancellationException])
     */
    protected open fun onCancelled(cause: Throwable, handled: Boolean) {}

    @Suppress("UNCHECKED_CAST")
    protected final override fun onCompletionInternal(state: Any?) {
        if (state is CompletedExceptionally)
            onCancelled(state.cause, state.handled)
        else
            onCompleted(state as T)
    }

    internal open val defaultResumeMode: Int get() = MODE_ATOMIC_DEFAULT

    /**
     * Completes execution of this with coroutine with the specified result.
     */
    public final override fun resumeWith(result: Result<T>) {
        makeCompletingOnce(result.toState(), defaultResumeMode)
    }

    internal final override fun handleOnCompletionException(exception: Throwable) {
        handleCoroutineException(context, exception)
    }

    internal override fun nameString(): String {
        val coroutineName = context.coroutineName ?: return super.nameString()
        return "\"$coroutineName\":${super.nameString()}"
    }

    /**
     * Starts this coroutine with the given code [block] and [start] strategy.
     * This function shall be invoked at most once on this coroutine.
     *
     * First, this function initializes parent job from the `parentContext` of this coroutine that was passed to it
     * during construction. Second, it starts the coroutine based on [start] parameter:
     *
     * * [DEFAULT] uses [startCoroutineCancellable].
     * * [ATOMIC] uses [startCoroutine].
     * * [UNDISPATCHED] uses [startCoroutineUndispatched].
     * * [LAZY] does nothing.
     */
    public fun start(start: CoroutineStart, block: suspend () -> T) {
        initParentJob()
        start(block, this)
    }

    /**
     * Starts this coroutine with the given code [block] and [start] strategy.
     * This function shall be invoked at most once on this coroutine.
     *
     * First, this function initializes parent job from the `parentContext` of this coroutine that was passed to it
     * during construction. Second, it starts the coroutine based on [start] parameter:
     * 
     * * [DEFAULT] uses [startCoroutineCancellable].
     * * [ATOMIC] uses [startCoroutine].
     * * [UNDISPATCHED] uses [startCoroutineUndispatched].
     * * [LAZY] does nothing.
     */
    public fun <R> start(start: CoroutineStart, receiver: R, block: suspend R.() -> T) {
        initParentJob()
        start(block, receiver, this)
    }
}
