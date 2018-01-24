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

import kotlinx.coroutines.experimental.CoroutineStart.*
import kotlinx.coroutines.experimental.intrinsics.*
import kotlin.coroutines.experimental.*

/**
 * Abstract base class for implementation of coroutines in coroutine builders.
 *
 * This class implements completion [Continuation], [Job], and [CoroutineScope] interfaces.
 * It stores the result of continuation in the state of the job.
 * This coroutine waits for children coroutines to finish before completing and
 * is cancelled through an intermediate _cancelling_ state.
 *
 * The following methods are available for override:
 *
 * * [onStart] is invoked when coroutine is create in not active state and is [started][Job.start].
 * * [onCancellation] is invoked as soon as coroutine is [cancelled][cancel] (becomes _cancelling_)
 *   or when it completes for any reason.
 * * [onCompleted] is invoked when coroutine completes with a value.
 * * [onCompletedExceptionally] in invoked when coroutines completes with exception.
 *
 * @param parentContext context of the parent coroutine.
 * @param active when `true` (by default) coroutine is created in _active_ state, when `false` in _new_ state.
 *               See [Job] for details.
 */
@Suppress("EXPOSED_SUPER_CLASS")
public abstract class AbstractCoroutine<in T>(
    private val parentContext: CoroutineContext,
    active: Boolean = true
) : JobSupport(active), Job, Continuation<T>, CoroutineScope {
    @Suppress("LeakingThis")
    public final override val context: CoroutineContext = parentContext + this
    public final override val coroutineContext: CoroutineContext get() = context

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
     * This function is invoked once when this coroutine is cancelled or is completed,
     * similarly to [invokeOnCompletion] with `onCancelling` set to `true`.
     *
     * @param cause the cause that was passed to [Job.cancel] function or `null` if coroutine was cancelled
     *              without cause or is completing normally.
     */
    protected open fun onCancellation(cause: Throwable?) {}

    internal override fun onCancellationInternal(exceptionally: CompletedExceptionally?) {
        onCancellation(exceptionally?.cause)
    }

    /**
     * This function is invoked once when job is completed normally with the specified [value].
     */
    protected open fun onCompleted(value: T) {}

    /**
     * This function is invoked once when job is completed exceptionally with the specified [exception].
     */
    protected open fun onCompletedExceptionally(exception: Throwable) {}

    @Suppress("UNCHECKED_CAST")
    internal override fun onCompletionInternal(state: Any?, mode: Int) {
        if (state is CompletedExceptionally)
            onCompletedExceptionally(state.exception)
        else
            onCompleted(state as T)
    }

    internal open val defaultResumeMode: Int get() = MODE_ATOMIC_DEFAULT

    /**
     * Completes execution of this coroutine normally with the specified [value].
     */
    public final override fun resume(value: T) {
        makeCompletingOnce(value, defaultResumeMode)
    }

    /**
     * Completes execution of this with coroutine exceptionally with the specified [exception].
     */
    public final override fun resumeWithException(exception: Throwable) {
        makeCompletingOnce(CompletedExceptionally(exception), defaultResumeMode)
    }

    internal final override fun handleException(exception: Throwable) {
        handleCoroutineException(parentContext, exception)
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

    // todo: This workaround for KT-21968, should be removed in the future
    override fun invokeOnCompletion(
        onCancelling: Boolean,
        invokeImmediately: Boolean,
        handler: CompletionHandler
    ): DisposableHandle =
        super.invokeOnCompletion(onCancelling, invokeImmediately, handler)

    // todo: This workaround for KT-21968, should be removed in the future
    override fun cancel(cause: Throwable?) =
        super.cancel(cause)
}

