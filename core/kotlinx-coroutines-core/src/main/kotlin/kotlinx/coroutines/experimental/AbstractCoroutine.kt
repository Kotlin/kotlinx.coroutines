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
 *  * Coroutines implement completion [Continuation], [Job], and [CoroutineScope] interfaces.
 *  * Coroutine stores the result of continuation in the state of the job.
 *  * Coroutine waits for children coroutines to finish before completing.
 *  * Coroutines are cancelled through an intermediate _cancelling_ state.
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

    internal final override fun onCancellationInternal(exceptionally: CompletedExceptionally?) {
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

    /**
     * Override for post-completion actions that need to do something with the state.
     * @param mode completion mode.
     * @suppress **This is unstable API and it is subject to change.**
     */
    @Suppress("UNCHECKED_CAST")
    internal override fun afterCompletion(state: Any?, mode: Int) {
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
     * Starts the corresponding block as a coroutine with this coroutine start strategy.
     *
     * First, this function initializes parent job from the `parentContext` of this coroutine that was passed to it
     * during construction. Second, it starts the coroutine based on [start] parameter:
     *
     * * [DEFAULT] uses [startCoroutineCancellable].
     * * [ATOMIC] uses [startCoroutine].
     * * [UNDISPATCHED] uses [startCoroutineUndispatched].
     * * [LAZY] does nothing.
     *
     * This function shall be invoked at most once.
     */
    public fun start(start: CoroutineStart, block: suspend () -> T) {
        initParentJob()
        @Suppress("DEPRECATION")
        start(block, this)
    }

    /**
     * Starts the corresponding block with receiver as a coroutine with this coroutine start strategy.
     *
     * First, this function initializes parent job from the `parentContext` of this coroutine that was passed to it
     * during construction. Second, it starts the coroutine based on [start] parameter:
     * 
     * * [DEFAULT] uses [startCoroutineCancellable].
     * * [ATOMIC] uses [startCoroutine].
     * * [UNDISPATCHED] uses [startCoroutineUndispatched].
     * * [LAZY] does nothing.
     *
     * This function shall be invoked at most once.
     */
    public fun <R> start(start: CoroutineStart, receiver: R, block: suspend R.() -> T) {
        initParentJob()
        @Suppress("DEPRECATION")
        start(block, receiver, this)
    }
}

