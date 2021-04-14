/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("DEPRECATION_ERROR")

package kotlinx.coroutines

import kotlinx.coroutines.CoroutineStart.*
import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.*

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
 * * [onStart] is invoked when the coroutine was created in non-active state and is being [started][Job.start].
 * * [onCancelling] is invoked as soon as the coroutine starts being cancelled for any reason (or completes).
 * * [onCompleted] is invoked when the coroutine completes with a value.
 * * [onCancelled] in invoked when the coroutine completes with an exception (cancelled).
 *
 * @param parentContext the context of the parent coroutine.
 * @param initParentJob specifies whether the parent-child relationship should be instantiated directly
 *               in `AbstractCoroutine` constructor. If set to `false`, it's the responsibility of the child class
 *               to invoke [initParentJob] manually.
 * @param active when `true` (by default), the coroutine is created in the _active_ state, otherwise it is created in the _new_ state.
 *               See [Job] for details.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public abstract class AbstractCoroutine<in T>(
    parentContext: CoroutineContext,
    initParentJob: Boolean,
    active: Boolean
) : JobSupport(active), Job, Continuation<T>, CoroutineScope {

    init {
        /*
         * Setup parent-child relationship between the parent in the context and the current coroutine.
         * It may cause this coroutine to become _cancelling_ if the parent is already cancelled.
         * It is dangerous to install parent-child relationship here if the coroutine class
         * operates its state from within onCancelled or onCancelling
         * (with exceptions for rx integrations that can't have any parent)
         */
        if (initParentJob) initParentJob(parentContext[Job])
    }

    /**
     * The context of this coroutine that includes this coroutine as a [Job].
     */
    @Suppress("LeakingThis")
    public final override val context: CoroutineContext = parentContext + this

    /**
     * The context of this scope which is the same as the [context] of this coroutine.
     */
    public override val coroutineContext: CoroutineContext get() = context

    override val isActive: Boolean get() = super.isActive

    /**
     * This function is invoked once when the job was completed normally with the specified [value],
     * right before all the waiters for the coroutine's completion are notified.
     */
    protected open fun onCompleted(value: T) {}

    /**
     * This function is invoked once when the job was cancelled with the specified [cause],
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

    override fun cancellationExceptionMessage(): String = "$classSimpleName was cancelled"

    @Suppress("UNCHECKED_CAST")
    protected final override fun onCompletionInternal(state: Any?) {
        if (state is CompletedExceptionally)
            onCancelled(state.cause, state.handled)
        else
            onCompleted(state as T)
    }

    /**
     * Completes execution of this with coroutine with the specified result.
     */
    public final override fun resumeWith(result: Result<T>) {
        val state = makeCompletingOnce(result.toState())
        if (state === COMPLETING_WAITING_CHILDREN) return
        afterResume(state)
    }

    protected open fun afterResume(state: Any?): Unit = afterCompletion(state)

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
     * * [DEFAULT] uses [startCoroutineCancellable].
     * * [ATOMIC] uses [startCoroutine].
     * * [UNDISPATCHED] uses [startCoroutineUndispatched].
     * * [LAZY] does nothing.
     */
    public fun <R> start(start: CoroutineStart, receiver: R, block: suspend R.() -> T) {
        start(block, receiver, this)
    }
}
