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

import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.loop
import kotlinx.coroutines.experimental.internal.LockFreeLinkedListHead
import kotlinx.coroutines.experimental.internal.LockFreeLinkedListNode
import kotlinx.coroutines.experimental.internal.OpDescriptor
import kotlinx.coroutines.experimental.intrinsics.startCoroutineUndispatched
import kotlinx.coroutines.experimental.selects.SelectBuilder
import kotlinx.coroutines.experimental.selects.SelectInstance
import kotlinx.coroutines.experimental.selects.select
import java.util.concurrent.Future
import kotlin.coroutines.experimental.AbstractCoroutineContextElement
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.CoroutineContext

// --------------- core job interfaces ---------------

/**
 * A background job. Conceptually, a job is a cancellable thing with a simple life-cycle that
 * culminates in its completion. Jobs can be arranged into parent-child hierarchies where cancellation
 * or completion of parent immediately cancels all its children.
 *
 * The most basic instances of [Job] are created with [launch] coroutine builder or with a
 * `Job()` factory function.  Other coroutine builders and primitives like
 * [Deferred] also implement [Job] interface.
 *
 * A job has the following states:
 *
 * | **State**                               | [isActive] | [isCompleted] | [isCancelled] |
 * | --------------------------------------- | ---------- | ------------- | ------------- |
 * | _New_ (optional initial state)          | `false`    | `false`       | `false`       |
 * | _Active_ (default initial state)        | `true`     | `false`       | `false`       |
 * | _Cancelling_ (optional transient state) | `false`    | `false`       | `true`        |
 * | _Cancelled_ (final state)               | `false`    | `true`        | `true`        |
 * | _Completed normally_ (final state)      | `false`    | `true`        | `false`       |
 *
 * Usually, a job is created in _active_ state (it is created and started). However, coroutine builders
 * that provide an optional `start` parameter create a coroutine in _new_ state when this parameter is set to
 * [CoroutineStart.LAZY]. Such a job can be made _active_ by invoking [start] or [join].
 *
 * A job can be _cancelled_ at any time with [cancel] function that forces it to transition to
 * _cancelling_ state immediately. Simple jobs, that are not backed by a coroutine, like
 * [CompletableDeferred] and the result of `Job()` factory function, don't
 * have a _cancelling_ state, but become _cancelled_ on [cancel] immediately.
 * Coroutines, on the other hand, become _cancelled_ only when they finish executing their code.
 *
 * ```
 *    +-----+       start      +--------+   complete   +-----------+
 *    | New | ---------------> | Active | -----------> | Completed |
 *    +-----+                  +--------+              | normally  |
 *       |                         |                   +-----------+
 *       | cancel                  | cancel
 *       V                         V
 *  +-----------+   finish   +------------+
 *  | Cancelled | <--------- | Cancelling |
 *  |(completed)|            +------------+
 *  +-----------+
 * ```
 *
 * A job in the coroutine [context][CoroutineScope.context] represents the coroutine itself.
 * A job is active while the coroutine is working and job's cancellation aborts the coroutine when
 * the coroutine is suspended on a _cancellable_ suspension point by throwing [CancellationException]
 * or the cancellation cause inside the coroutine.
 *
 * A job can have a _parent_ job. A job with a parent is cancelled when its parent is cancelled or completes.
 *
 * All functions on this interface and on all interfaces derived from it are **thread-safe** and can
 * be safely invoked from concurrent coroutines without external synchronization.
 */
public interface Job : CoroutineContext.Element {
    /**
     * Key for [Job] instance in the coroutine context.
     */
    public companion object Key : CoroutineContext.Key<Job> {
        /**
         * Creates a new job object in _active_ state.
         * It is optionally a child of a [parent] job.
         * @suppress **Deprecated**
         */
        @Deprecated("Replaced with top-level function", level = DeprecationLevel.HIDDEN)
        public operator fun invoke(parent: Job? = null): Job = Job(parent)

        init {
            /*
             * Here we make sure that CoroutineExceptionHandler is always initialized in advance, so
             * that if a coroutine fails due to StackOverflowError we don't fail to report this error
             * trying to initialize CoroutineExceptionHandler
             */
            CoroutineExceptionHandler
        }
    }

    // ------------ state query ------------

    /**
     * Returns `true` when this job is active -- it was already started and has not completed or cancelled yet.
     */
    public val isActive: Boolean

    /**
     * Returns `true` when this job has completed for any reason. A job that was cancelled and has
     * finished its execution is also considered complete.
     */
    public val isCompleted: Boolean

    /**
     * Returns `true` if this job was [cancelled][cancel]. In the general case, it does not imply that the
     * job has already [completed][isCompleted] (it may still be cancelling whatever it was doing).
     */
    public val isCancelled: Boolean

    /**
     * Returns the exception that signals the completion of this job -- it returns the original
     * [cancel] cause or an instance of [CancellationException] if this job had completed
     * normally or was cancelled without a cause. This function throws
     * [IllegalStateException] when invoked for an job that has not [completed][isCompleted] nor
     * [isCancelled] yet.
     *
     * The [cancellable][suspendCancellableCoroutine] suspending functions throw this exception
     * when trying to suspend in the context of this job.
     */
    public fun getCompletionException(): Throwable

    // ------------ state update ------------

    /**
     * Starts coroutine related to this job (if any) if it was not started yet.
     * The result `true` if this invocation actually started coroutine or `false`
     * if it was already started or completed.
     */
    public fun start(): Boolean

    /**
     * Cancel this job with an optional cancellation [cause]. The result is `true` if this job was
     * cancelled as a result of this invocation and `false` otherwise
     * (if it was already _completed_ or if it is [NonCancellable]).
     * Repeated invocations of this function have no effect and always produce `false`.
     *
     * When cancellation has a clear reason in the code, an instance of [CancellationException] should be created
     * at the corresponding original cancellation site and passed into this method to aid in debugging by providing
     * both the context of cancellation and text description of the reason.
     */
    public fun cancel(cause: Throwable? = null): Boolean

    // ------------ state waiting ------------

    /**
     * Suspends coroutine until this job is complete. This invocation resumes normally (without exception)
     * when the job is complete for any reason. This function also [starts][Job.start] the corresponding coroutine
     * if the [Job] was still in _new_ state.
     *
     * This suspending function is cancellable. If the [Job] of the invoking coroutine is cancelled or completed while this
     * suspending function is suspended, this function immediately resumes with [CancellationException].
     *
     * This function can be used in [select] invocation with [onJoin][SelectBuilder.onJoin] clause.
     * Use [isCompleted] to check for completion of this job without waiting.
     */
    public suspend fun join()

    // ------------ low-level state-notification ------------

    /**
     * Registers handler that is **synchronously** invoked once on completion of this job.
     * When job is already complete, then the handler is immediately invoked
     * with a job's cancellation cause or `null`. Otherwise, handler will be invoked once when this
     * job is complete.
     *
     * The resulting [DisposableHandle] can be used to [dispose][DisposableHandle.dispose] the
     * registration of this handler and release its memory if its invocation is no longer needed.
     * There is no need to dispose the handler after completion of this job. The references to
     * all the handlers are released when this job completes.
     *
     * Note, that the handler is not invoked on invocation of [cancel] when
     * job becomes _cancelling_, but only when the corresponding coroutine had finished execution
     * of its code and became _cancelled_. There is an overloaded version of this function
     * with `onCancelling` parameter to receive notification on _cancelling_ state.
     *
     * **Note**: This function is a part of internal machinery that supports parent-child hierarchies
     * and allows for implementation of suspending functions that wait on the Job's state.
     * This function should not be used in general application code.
     * Implementations of `CompletionHandler` must be fast and _lock-free_.
     */
    public fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle

    /**
     * Registers handler that is **synchronously** invoked once on cancellation or completion of this job.
     * When job is already complete, then the handler is immediately invoked
     * with a job's cancellation cause or `null`. Otherwise, handler will be invoked once when this
     * job is cancelled or complete.
     *
     * Invocation of this handler on a transition to a transient _cancelling_ state
     * is controlled by [onCancelling] boolean parameter.
     * The handler is invoked on invocation of [cancel] when
     * job becomes _cancelling_ when [onCancelling] parameters is set to `true`. However,
     * when this [Job] is not backed by a coroutine, like [CompletableDeferred] or [CancellableContinuation]
     * (both of which do not posses a _cancelling_ state), then the value of [onCancelling] parameter is ignored.
     *
     * The resulting [DisposableHandle] can be used to [dispose][DisposableHandle.dispose] the
     * registration of this handler and release its memory if its invocation is no longer needed.
     * There is no need to dispose the handler after completion of this job. The references to
     * all the handlers are released when this job completes.
     *
     * **Note**: This function is a part of internal machinery that supports parent-child hierarchies
     * and allows for implementation of suspending functions that wait on the Job's state.
     * This function should not be used in general application code.
     * Implementations of `CompletionHandler` must be fast and _lock-free_.
     */
    public fun invokeOnCompletion(handler: CompletionHandler, onCancelling: Boolean): DisposableHandle

    // ------------ unstable internal API ------------

    /**
     * Registers [onJoin][SelectBuilder.onJoin] select clause.
     * @suppress **This is unstable API and it is subject to change.**
     */
    public fun <R> registerSelectJoin(select: SelectInstance<R>, block: suspend () -> R)

    /**
     * @suppress **Error**: Operator '+' on two Job objects is meaningless.
     * Job is a coroutine context element and `+` is a set-sum operator for coroutine contexts.
     * The job to the right of `+` just replaces the job the left of `+`.
     */
    @Suppress("DeprecatedCallableAddReplaceWith")
    @Deprecated(message = "Operator '+' on two Job objects is meaningless. " +
                    "Job is a coroutine context element and `+` is a set-sum operator for coroutine contexts. " +
                    "The job to the right of `+` just replaces the job the left of `+`.",
            level = DeprecationLevel.ERROR)
    public operator fun plus(other: Job) = other

    /**
     * Registration object for [invokeOnCompletion]. It can be used to [unregister] if needed.
     * There is no need to unregister after completion.
     * @suppress **Deprecated**: Replace with `DisposableHandle`
     */
    @Deprecated(message = "Replace with `DisposableHandle`",
        replaceWith = ReplaceWith("DisposableHandle"))
    public interface Registration {
        /**
         * Unregisters completion handler.
         * @suppress **Deprecated**: Replace with `dispose`
         */
        @Deprecated(message = "Replace with `dispose`",
            replaceWith = ReplaceWith("dispose()"))
        public fun unregister()
    }
}

/**
 * Creates a new job object in an _active_ state.
 * It is optionally a child of a [parent] job.
 */
public fun Job(parent: Job? = null): Job = JobImpl(parent)

/**
 * A handle to an allocated object that can be disposed to make it eligible for garbage collection.
 */
@Suppress("DEPRECATION") // todo: remove when Job.Registration is removed
public interface DisposableHandle : Job.Registration {
    /**
     * Disposes the corresponding object, making it eligible for garbage collection.
     * Repeated invocation of this function has no effect.
     */
    public fun dispose()

    /**
     * Unregisters completion handler.
     * @suppress **Deprecated**: Replace with `dispose`
     */
    @Deprecated(message = "Replace with `dispose`",
        replaceWith = ReplaceWith("dispose()"))
    public override fun unregister() = dispose()
}

/**
 * Handler for [Job.invokeOnCompletion].
 *
 * **Note**: This type is a part of internal machinery that supports parent-child hierarchies
 * and allows for implementation of suspending functions that wait on the Job's state.
 * This type should not be used in general application code.
 * Implementations of `CompletionHandler` must be fast and _lock-free_.
 */
public typealias CompletionHandler = (Throwable?) -> Unit

/**
 * Thrown by cancellable suspending functions if the [Job] of the coroutine is cancelled while it is suspending.
 */
public typealias CancellationException = java.util.concurrent.CancellationException

/**
 * Unregisters a specified [registration] when this job is complete.
 *
 * This is a shortcut for the following code with slightly more efficient implementation (one fewer object created).
 * ```
 * invokeOnCompletion { registration.unregister() }
 * ```
 * @suppress: **Deprecated**: Renamed to `disposeOnCompletion`.
 */
@Deprecated(message = "Renamed to `disposeOnCompletion`",
    replaceWith = ReplaceWith("disposeOnCompletion(registration)"))
public fun Job.unregisterOnCompletion(registration: DisposableHandle): DisposableHandle =
    invokeOnCompletion(DisposeOnCompletion(this, registration))

/**
 * Disposes a specified [handle] when this job is complete.
 *
 * This is a shortcut for the following code with slightly more efficient implementation (one fewer object created).
 * ```
 * invokeOnCompletion { handle.dispose() }
 * ```
 */
public fun Job.disposeOnCompletion(handle: DisposableHandle): DisposableHandle =
    invokeOnCompletion(DisposeOnCompletion(this, handle))

/**
 * Cancels a specified [future] when this job is complete.
 *
 * This is a shortcut for the following code with slightly more efficient implementation (one fewer object created).
 * ```
 * invokeOnCompletion { future.cancel(false) }
 * ```
 */
public fun Job.cancelFutureOnCompletion(future: Future<*>): DisposableHandle =
    invokeOnCompletion(CancelFutureOnCompletion(this, future))

/**
 * @suppress **Deprecated**: `join` is now a member function of `Job`.
 */
@Suppress("EXTENSION_SHADOWED_BY_MEMBER", "DeprecatedCallableAddReplaceWith")
@Deprecated(message = "`join` is now a member function of `Job`")
public suspend fun Job.join() = this.join()

/**
 * No-op implementation of [Job.Registration].
 */
@Deprecated(message = "Replace with `NonDisposableHandle`",
    replaceWith = ReplaceWith("NonDisposableHandle"))
typealias EmptyRegistration = NonDisposableHandle

/**
 * No-op implementation of [DisposableHandle].
 */
public object NonDisposableHandle : DisposableHandle {
    /** Does not do anything. */
    override fun dispose() {}

    /** Returns "NonDisposableHandle" string. */
    override fun toString(): String = "NonDisposableHandle"
}

// --------------- utility classes to simplify job implementation

/**
 * A concrete implementation of [Job]. It is optionally a child to a parent job.
 * This job is cancelled when the parent is complete, but not vise-versa.
 *
 * This is an open class designed for extension by more specific classes that might augment the
 * state and mare store addition state information for completed jobs, like their result values.
 *
 * @param active when `true` the job is created in _active_ state, when `false` in _new_ state. See [Job] for details.
 * @suppress **This is unstable API and it is subject to change.**
 */
public open class JobSupport(active: Boolean) : AbstractCoroutineContextElement(Job), Job {
    /*
       === Internal states ===

       name       state class    public state  description
       ------     ------------   ------------  -----------
       EMPTY_N    EmptyNew     : New           no listeners
       EMPTY_A    EmptyActive  : Active        no listeners
       SINGLE     JobNode      : Active        a single listener
       SINGLE+    JobNode      : Active        a single listener + NodeList added as its next
       LIST_N     NodeList     : New           a list of listeners (promoted once, does not got back to EmptyNew)
       LIST_A     NodeList     : Active        a list of listeners (promoted once, does not got back to JobNode/EmptyActive)
       CANCELLING Cancelling   : Cancelling(*) a list of listeners (promoted once)
       FINAL_C    Cancelled    : Cancelled     cancelled (final state)
       FINAL_F    Failed       : Completed     failed for other reason (final state)
       FINAL_R    <any>        : Completed     produced some result

       === Transitions ===

           New states      Active states     Inactive states
          +---------+       +---------+       +----------+
          | EMPTY_N | --+-> | EMPTY_A | --+-> |  FINAL_* |
          +---------+   |   +---------+   |   +----------+
               |        |     |     ^     |
               |        |     V     |     |
               |        |   +---------+   |
               |        |   | SINGLE  | --+
               |        |   +---------+   |
               |        |        |        |
               |        |        V        |
               |        |   +---------+   |
               |        +-- | SINGLE+ | --+
               |            +---------+   |
               |                 |        |
               V                 V        |
          +---------+       +---------+   |
          | LIST_N  | ----> | LIST_A  | --+
          +---------+       +---------+   |
               |                |         |
               |                V         |
               |         +------------+   |
               +-------> | CANCELLING | --+
                         +------------+

       This state machine and its transition matrix are optimized for the common case when job is created in active
       state (EMPTY_A) and at most one completion listener is added to it during its life-time.

       Note, that the actual `_state` variable can also be a reference to atomic operation descriptor `OpDescriptor`

       (*) The CANCELLING state is used only in AbstractCoroutine class. A general Job (that does not
           extend AbstractCoroutine) does not have CANCELLING state. It immediately transitions to
           FINAL_C (Cancelled) state on cancellation/completion
     */

    // Note: use shared objects while we have no listeners
    private val _state = atomic<Any?>(if (active) EmptyActive else EmptyNew)

    @Volatile
    private var parentHandle: DisposableHandle? = null

    // ------------ initialization ------------

    /**
     * Initializes parent job.
     * It shall be invoked at most once after construction after all other initialization.
     */
    public fun initParentJob(parent: Job?) {
        check(parentHandle == null)
        if (parent == null) {
            parentHandle = NonDisposableHandle
            return
        }
        parent.start() // make sure the parent is started
        // directly pass HandlerNode to parent scope to optimize one closure object (see makeNode)
        val newRegistration = parent.invokeOnCompletion(ParentOnCancellation(parent), onCancelling = true)
        parentHandle = newRegistration
        // now check our state _after_ registering (see updateState order of actions)
        if (isCompleted) newRegistration.dispose()
    }

    private inner class ParentOnCancellation(parent: Job) : JobCancellationNode<Job>(parent) {
        override fun invokeOnce(reason: Throwable?) { onParentCancellation(reason) }
        override fun toString(): String = "ParentOnCancellation[${this@JobSupport}]"
    }

    /**
     * Invoked at most once on parent completion.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun onParentCancellation(cause: Throwable?) {
        // if parent was completed with CancellationException then use it as the cause of our cancellation, too.
        // however, we shall not use application specific exceptions here. So if parent crashes due to IOException,
        // we cannot and should not cancel the child with IOException
        cancel(cause as? CancellationException)
    }

    // ------------ state query ------------

    /**
     * Returns current state of this job.
     */
    protected val state: Any? get() {
        _state.loop { state -> // helper loop on state (complete in-progress atomic operations)
            if (state !is OpDescriptor) return state
            state.perform(this)
        }
    }

    protected inline fun loopOnState(block: (Any?) -> Unit): Nothing {
        while (true) {
            block(state)
        }
    }

    public final override val isActive: Boolean get() {
        val state = this.state
        return state is Incomplete && state.isActive
    }

    public final override val isCompleted: Boolean get() = state !is Incomplete

    public final override val isCancelled: Boolean get() {
        val state = this.state
        return state is Cancelled || state is Cancelling
    }

    // ------------ state update ------------

    /**
     * Updates current [state] of this job.
     */
    protected fun updateState(expect: Any, proposedUpdate: Any?, mode: Int): Boolean {
        val update = coerceProposedUpdate(expect, proposedUpdate)
        if (!tryUpdateState(expect, update)) return false
        completeUpdateState(expect, update, mode)
        // if an exceptional completion was suppressed (because cancellation was in progress), then report it separately
        if (proposedUpdate !== update && proposedUpdate is CompletedExceptionally && proposedUpdate.cause != null)
            handleException(proposedUpdate.cause)
        return true
    }

    // when Job is in Cancelling state, it can only be promoted to Cancelled state with the same cause
    // however, null cause can be replaced with more specific CancellationException (that contains stack trace)
    private fun coerceProposedUpdate(expect: Any, proposedUpdate: Any?): Any? =
        if (expect is Cancelling && !correspondinglyCancelled(expect, proposedUpdate))
            expect.cancelled else proposedUpdate

    private fun correspondinglyCancelled(expect: Cancelling, proposedUpdate: Any?): Boolean {
        if (proposedUpdate !is Cancelled) return false
        return proposedUpdate.cause === expect.cancelled.cause ||
            proposedUpdate.cause is CancellationException && expect.cancelled.cause == null
    }

    /**
     * Tries to initiate update of the current [state] of this job.
     */
    protected fun tryUpdateState(expect: Any, update: Any?): Boolean  {
        require(expect is Incomplete && update !is Incomplete) // only incomplete -> completed transition is allowed
        if (!_state.compareAndSet(expect, update)) return false
        // Unregister from parent job
        parentHandle?.dispose() // volatile read parentHandle _after_ state was updated
        return true // continues in completeUpdateState
    }

    /**
     * Completes update of the current [state] of this job.
     */
    protected fun completeUpdateState(expect: Any, update: Any?, mode: Int) {
        // Invoke completion handlers
        val cause = (update as? CompletedExceptionally)?.cause
        when (expect) {
            is JobNode<*> -> try { // SINGLE/SINGLE+ state -- one completion handler (common case)
                expect.invoke(cause)
            } catch (ex: Throwable) {
                handleException(ex)
            }
            is NodeList -> notifyCompletion(expect, cause) // LIST state -- a list of completion handlers
            is Cancelling -> notifyCompletion(expect.list, cause) // has list, too
            // otherwise -- do nothing (it was Empty*)
            else -> check(expect is Empty)
        }
        // Do overridable processing after completion handlers
        if (expect !is Cancelling) onCancellation() // only notify when was not cancelling before
        afterCompletion(update, mode)
    }

    private inline fun <reified T: JobNode<*>> notifyHandlers(list: NodeList, cause: Throwable?) {
        var exception: Throwable? = null
        list.forEach<T> { node ->
            try {
                node.invoke(cause)
            } catch (ex: Throwable) {
                exception?.apply { addSuppressed(ex) } ?: run { exception = ex }
            }

        }
        exception?.let { handleException(it) }
    }

    private fun notifyCompletion(list: NodeList, cause: Throwable?) =
        notifyHandlers<JobNode<*>>(list, cause)

    private fun notifyCancellation(list: NodeList, cause: Throwable?) =
        notifyHandlers<JobCancellationNode<*>>(list, cause)

    public final override fun start(): Boolean {
        loopOnState { state ->
            when (startInternal(state)) {
                FALSE -> return false
                TRUE -> return true
            }
        }
    }

    // returns: RETRY/FALSE/TRUE:
    //   FALSE when not new,
    //   TRUE  when started
    //   RETRY when need to retry
    private fun startInternal(state: Any?): Int {
        when (state) {
            is Empty -> { // EMPTY_X state -- no completion handlers
                if (state.isActive) return FALSE // already active
                if (!_state.compareAndSet(state, EmptyActive)) return RETRY
                onStart()
                return TRUE
            }
            is NodeList -> { // LIST -- a list of completion handlers (either new or active)
                if (state._active.value != 0) return FALSE
                if (!state._active.compareAndSet(0, 1)) return RETRY
                onStart()
                return TRUE
            }
            else -> return FALSE // not a new state
        }
    }

    /**
     * Override to provide the actual [start] action.
     */
    protected open fun onStart() {}

    public final override fun getCompletionException(): Throwable  {
        val state = this.state
        return when (state) {
            is Cancelling -> state.cancelled.exception
            is Incomplete -> error("Job was not completed or cancelled yet")
            is CompletedExceptionally -> state.exception
            else -> CancellationException("Job has completed normally")
        }
    }

    /**
     * Returns the cause that signals the completion of this job -- it returns the original
     * [cancel] cause or **`null` if this job had completed
     * normally or was cancelled without a cause**. This function throws
     * [IllegalStateException] when invoked for an job that has not [completed][isCompleted] nor
     * [isCancelled] yet.
     */
    protected fun getCompletionCause(): Throwable? {
        val state = this.state
        return when (state) {
            is Cancelling -> state.cancelled.cause
            is Incomplete -> error("Job was not completed or cancelled yet")
            is CompletedExceptionally -> state.cause
            else -> null
        }
    }

    public final override fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle =
        installHandler(handler, onCancelling = false)

    public final override fun invokeOnCompletion(handler: CompletionHandler, onCancelling: Boolean): DisposableHandle =
        installHandler(handler, onCancelling = onCancelling && hasCancellingState)

    private fun installHandler(handler: CompletionHandler, onCancelling: Boolean): DisposableHandle {
        var nodeCache: JobNode<*>? = null
        loopOnState { state ->
            when (state) {
                is Empty -> { // EMPTY_X state -- no completion handlers
                    if (state.isActive) {
                        // try move to SINGLE state
                        val node = nodeCache ?: makeNode(handler, onCancelling).also { nodeCache = it }
                        if (_state.compareAndSet(state, node)) return node
                    } else
                        promoteEmptyToNodeList(state) // that way we can add listener for non-active coroutine
                }
                is JobNode<*> -> { // SINGLE/SINGLE+ state -- one completion handler
                    promoteSingleToNodeList(state)
                }
                is NodeList -> { // LIST -- a list of completion handlers (either new or active)
                    val node = nodeCache ?: makeNode(handler, onCancelling).also { nodeCache = it }
                    if (addLastAtomic(state, state, node)) return node
                }
                is Cancelling -> { // CANCELLING -- has a list of completion handlers
                    if (onCancelling) { // installing cancellation handler on job that is being cancelled
                        handler((state as? CompletedExceptionally)?.exception)
                        return NonDisposableHandle
                    }
                    val node = nodeCache ?: makeNode(handler, onCancelling).also { nodeCache = it }
                    if (addLastAtomic(state, state.list, node)) return node
                }
                else -> { // is inactive
                    handler((state as? CompletedExceptionally)?.exception)
                    return NonDisposableHandle
                }
            }
        }
    }

    private fun makeNode(handler: CompletionHandler, onCancelling: Boolean): JobNode<*> =
        if (onCancelling)
            (handler as? JobCancellationNode<*>)?.also { require(it.job === this) }
                ?: InvokeOnCancellation(this, handler)
        else
            (handler as? JobNode<*>)?.also { require(it.job === this && (!hasCancellingState || it !is JobCancellationNode)) }
                ?: InvokeOnCompletion(this, handler)


    private fun addLastAtomic(expect: Any, list: NodeList, node: JobNode<*>) =
        list.addLastIf(node) { this.state === expect }

    private fun promoteEmptyToNodeList(state: Empty) {
        // try to promote it to list in new state
        _state.compareAndSet(state, NodeList(state.isActive))
    }

    private fun promoteSingleToNodeList(state: JobNode<*>) {
        // try to promote it to list (SINGLE+ state)
        state.addOneIfEmpty(NodeList(active = true))
        // it must be in SINGLE+ state or state has changed (node could have need removed from state)
        val list = state.next // either NodeList or somebody else won the race, updated state
        // just attempt converting it to list if state is still the same, then we'll continue lock-free loop
        _state.compareAndSet(state, list)
    }

    final override suspend fun join() {
        if (!joinInternal()) return // fast-path no wait
        return joinSuspend() // slow-path wait
    }

    private fun joinInternal(): Boolean {
        loopOnState { state ->
            if (state !is Incomplete) return false // not active anymore (complete) -- no need to wait
            if (startInternal(state) >= 0) return true // wait unless need to retry
        }
    }

    private suspend fun joinSuspend() = suspendCancellableCoroutine<Unit> { cont ->
        cont.disposeOnCompletion(invokeOnCompletion(ResumeOnCompletion(this, cont)))
    }

    override fun <R> registerSelectJoin(select: SelectInstance<R>, block: suspend () -> R) {
        // fast-path -- check state and select/return if needed
        loopOnState { state ->
            if (select.isSelected) return
            if (state !is Incomplete) {
                // already complete -- select result
                if (select.trySelect(null))
                    block.startCoroutineUndispatched(select.completion)
                return
            }
            if (startInternal(state) == 0) {
                // slow-path -- register waiter for completion
                select.disposeOnSelect(invokeOnCompletion(SelectJoinOnCompletion(this, select, block)))
                return
            }
        }
    }

    internal fun removeNode(node: JobNode<*>) {
        // remove logic depends on the state of the job
        loopOnState { state ->
            when (state) {
                is JobNode<*> -> { // SINGE/SINGLE+ state -- one completion handler
                    if (state !== node) return // a different job node --> we were already removed
                    // try remove and revert back to empty state
                    if (_state.compareAndSet(state, EmptyActive)) return
                }
                is NodeList, is Cancelling -> { // LIST or CANCELLING -- a list of completion handlers
                    // remove node from the list
                    node.remove()
                    return
                }
                else -> return // it is inactive or Empty* (does not have any completion handlers)
            }
        }
    }

    protected open val hasCancellingState: Boolean get() = false

    public final override fun cancel(cause: Throwable?): Boolean =
        if (hasCancellingState)
            makeCancelling(cause) else
            makeCancelled(cause)

    // we will be dispatching coroutine to process its cancellation exception, so there is no need for
    // an extra check for Job status in MODE_CANCELLABLE
    private fun updateStateCancelled(state: Incomplete, cause: Throwable?) =
        updateState(state, Cancelled(cause), mode = MODE_ATOMIC_DEFAULT)

    // transitions to Cancelled state
    private fun makeCancelled(cause: Throwable?): Boolean {
        loopOnState { state ->
            if (state !is Incomplete) return false // quit if already complete
            if (updateStateCancelled(state, cause)) return true
        }
    }

    // transitions to Cancelling state
    private fun makeCancelling(cause: Throwable?): Boolean {
        loopOnState { state ->
            when (state) {
                is Empty -> { // EMPTY_X state -- no completion handlers
                    if (state.isActive) {
                        promoteEmptyToNodeList(state) // this way can wrap it into Cancelling on next pass
                    } else {
                        // cancelling a non-started coroutine makes it immediately cancelled
                        // (and we have no listeners to notify which makes it very simple)
                        if (updateStateCancelled(state, cause)) return true
                    }
                }
                is JobNode<*> -> { // SINGLE/SINGLE+ state -- one completion handler
                    promoteSingleToNodeList(state)
                }
                is NodeList -> { // LIST -- a list of completion handlers (either new or active)
                    if (state.isActive) {
                        // try make it cancelling on the condition that we're still in this state
                        if (_state.compareAndSet(state, Cancelling(state, Cancelled(cause)))) {
                            notifyCancellation(state, cause)
                            onCancellation()
                            return true
                        }
                    } else {
                        // cancelling a non-started coroutine makes it immediately cancelled
                        if (updateStateCancelled(state, cause))
                            return true
                    }
                }
                else -> { // is inactive or already cancelling
                    return false
                }
            }
        }
    }

    /**
     * Override to process any exceptions that were encountered while invoking completion handlers
     * installed via [invokeOnCompletion].
     */
    protected open fun handleException(exception: Throwable) {
        throw exception
    }

    /**
     * It is invoked once when job is cancelled or is completed, similarly to [invokeOnCompletion] with
     * `onCancelling` set to `true`.
     */
    protected open fun onCancellation() {}

    /**
     * Override for post-completion actions that need to do something with the state.
     * @param mode completion mode.
     */
    protected open fun afterCompletion(state: Any?, mode: Int) {}

    // for nicer debugging
    override fun toString(): String {
        val state = this.state
        val result = if (state is Incomplete) "" else "[$state]"
        return "${this::class.java.simpleName}{${stateToString(state)}}$result@${Integer.toHexString(System.identityHashCode(this))}"
    }

    /**
     * Interface for incomplete [state] of a job.
     */
    public interface Incomplete {
        val isActive: Boolean
    }

    private class Cancelling(
        @JvmField val list: NodeList,
        @JvmField val cancelled: Cancelled
    ) : Incomplete {
        override val isActive: Boolean get() = false
    }

    private class NodeList(
        active: Boolean
    ) : LockFreeLinkedListHead(), Incomplete {
        val _active = atomic(if (active) 1 else 0)

        override val isActive: Boolean get() = _active.value != 0

        override fun toString(): String = buildString {
            append("List")
            append(if (isActive) "{Active}" else "{New}")
            append("[")
            var first = true
            this@NodeList.forEach<JobNode<*>> { node ->
                if (first) first = false else append(", ")
                append(node)
            }
            append("]")
        }
    }

    /**
     * Class for a [state] of a job that had completed exceptionally, including cancellation.
     *
     * @param cause the exceptional completion cause. If `cause` is null, then a [CancellationException]
     *        if created on first get from [exception] property.
     */
    public open class CompletedExceptionally(
        @JvmField val cause: Throwable?
    ) {
        @Volatile
        private var _exception: Throwable? = cause // materialize CancellationException on first need

        /**
         * Returns completion exception.
         */
        public val exception: Throwable get() =
            _exception ?: // atomic read volatile var or else create new
                CancellationException("Job was cancelled").also { _exception = it }

        override fun toString(): String = "${this::class.java.simpleName}[$exception]"
    }

    /**
     * A specific subclass of [CompletedExceptionally] for cancelled jobs.
     */
    public class Cancelled(
        cause: Throwable?
    ) : CompletedExceptionally(cause)


    /*
     * =================================================================================================
     * This is ready-to-use implementation for Deferred interface.
     * However, it is not type-safe. Conceptually it just exposes the value of the underlying
     * completed state as `Any?`
     * =================================================================================================
     */

    public val isCompletedExceptionally: Boolean get() = state is CompletedExceptionally

    protected fun getCompletedInternal(): Any? {
        val state = this.state
        check(state !is Incomplete) { "This job has not completed yet" }
        if (state is CompletedExceptionally) throw state.exception
        return state
    }

    protected suspend fun awaitInternal(): Any? {
        // fast-path -- check state (avoid extra object creation)
        while(true) { // lock-free loop on state
            val state = this.state
            if (state !is Incomplete) {
                // already complete -- just return result
                if (state is CompletedExceptionally) throw state.exception
                return state

            }
            if (startInternal(state) >= 0) break // break unless needs to retry
        }
        return awaitSuspend() // slow-path
    }

    private suspend fun awaitSuspend(): Any? = suspendCancellableCoroutine { cont ->
        cont.disposeOnCompletion(invokeOnCompletion {
            val state = this.state
            check(state !is Incomplete)
            if (state is CompletedExceptionally)
                cont.resumeWithException(state.exception)
            else
                cont.resume(state)
        })
    }

    protected fun <R> registerSelectAwaitInternal(select: SelectInstance<R>, block: suspend (Any?) -> R) {
        // fast-path -- check state and select/return if needed
        loopOnState { state ->
            if (select.isSelected) return
            if (state !is Incomplete) {
                // already complete -- select result
                if (select.trySelect(null)) {
                    if (state is CompletedExceptionally)
                        select.resumeSelectCancellableWithException(state.exception)
                    else
                        block.startCoroutineUndispatched(state, select.completion)
                }
                return
            }
            if (startInternal(state) == 0) {
                // slow-path -- register waiter for completion
                select.disposeOnSelect(invokeOnCompletion(SelectAwaitOnCompletion(this, select, block)))
                return
            }
        }
    }

    internal fun <R> selectAwaitCompletion(select: SelectInstance<R>, block: suspend (Any?) -> R) {
        val state = this.state
        // Note: await is non-atomic (can be cancelled while dispatched)
        if (state is CompletedExceptionally)
            select.resumeSelectCancellableWithException(state.exception)
        else
            block.startCoroutineCancellable(state, select.completion)
    }
}

internal fun stateToString(state: Any?): String =
    if (state is JobSupport.Incomplete)
        if (state.isActive) "Active" else "New"
    else "Completed"

private const val RETRY = -1
private const val FALSE = 0
private const val TRUE = 1

private val EmptyNew = Empty(false)
private val EmptyActive = Empty(true)

private class Empty(override val isActive: Boolean) : JobSupport.Incomplete {
    override fun toString(): String = "Empty{${if (isActive) "Active" else "New" }}"
}

private class JobImpl(parent: Job? = null) : JobSupport(true) {
    init { initParentJob(parent) }
}

// -------- invokeOnCompletion nodes

internal abstract class JobNode<out J : Job>(
    @JvmField val job: J
) : LockFreeLinkedListNode(), DisposableHandle, CompletionHandler, JobSupport.Incomplete {
    final override val isActive: Boolean get() = true
    final override fun dispose() = (job as JobSupport).removeNode(this)
    override abstract fun invoke(reason: Throwable?)
}

private class InvokeOnCompletion(
    job: Job,
    private val handler: CompletionHandler
) : JobNode<Job>(job)  {
    override fun invoke(reason: Throwable?) = handler.invoke(reason)
    override fun toString() = "InvokeOnCompletion[${handler::class.java.name}@${Integer.toHexString(System.identityHashCode(handler))}]"
}

private class ResumeOnCompletion(
    job: Job,
    private val continuation: Continuation<Unit>
) : JobNode<Job>(job)  {
    override fun invoke(reason: Throwable?) = continuation.resume(Unit)
    override fun toString() = "ResumeOnCompletion[$continuation]"
}

internal class DisposeOnCompletion(
    job: Job,
    private val handle: DisposableHandle
) : JobNode<Job>(job) {
    override fun invoke(reason: Throwable?) = handle.dispose()
    override fun toString(): String = "DisposeOnCompletion[$handle]"
}

private class CancelFutureOnCompletion(
    job: Job,
    private val future: Future<*>
) : JobNode<Job>(job)  {
    override fun invoke(reason: Throwable?) {
        // Don't interrupt when cancelling future on completion, because no one is going to reset this
        // interruption flag and it will cause spurious failures elsewhere
        future.cancel(false)
    }
    override fun toString() = "CancelFutureOnCompletion[$future]"
}

private class SelectJoinOnCompletion<R>(
    job: JobSupport,
    private val select: SelectInstance<R>,
    private val block: suspend () -> R
) : JobNode<JobSupport>(job) {
    override fun invoke(reason: Throwable?) {
        if (select.trySelect(null))
            block.startCoroutineCancellable(select.completion)
    }
    override fun toString(): String = "SelectJoinOnCompletion[$select]"
}

private class SelectAwaitOnCompletion<R>(
    job: JobSupport,
    private val select: SelectInstance<R>,
    private val block: suspend (Any?) -> R
) : JobNode<JobSupport>(job) {
    override fun invoke(reason: Throwable?) {
        if (select.trySelect(null))
            job.selectAwaitCompletion(select, block)
    }
    override fun toString(): String = "SelectAwaitOnCompletion[$select]"
}

// -------- invokeOnCancellation nodes

internal abstract class JobCancellationNode<out J : Job>(job: J) : JobNode<J>(job) {
    // shall be invoked at most once, so here is an additional flag
    private val _invoked = atomic(0)

    final override fun invoke(reason: Throwable?) {
        if (_invoked.compareAndSet(0, 1)) invokeOnce(reason)
    }

    abstract fun invokeOnce(reason: Throwable?)
}

private class InvokeOnCancellation(
    job: Job,
    private val handler: CompletionHandler
) : JobCancellationNode<Job>(job)  {
    override fun invokeOnce(reason: Throwable?) = handler.invoke(reason)
    override fun toString() = "InvokeOnCancellation[${handler::class.java.name}@${Integer.toHexString(System.identityHashCode(handler))}]"
}

