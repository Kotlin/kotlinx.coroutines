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
import java.util.concurrent.Future
import java.util.concurrent.atomic.AtomicReferenceFieldUpdater
import kotlin.coroutines.experimental.AbstractCoroutineContextElement
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.CoroutineContext

// --------------- core job interfaces ---------------

/**
 * A background job. It is created with [launch] coroutine builder or with a
 * [`Job()`][Job.Key.invoke] factory function.
 * A job can be _cancelled_ at any time with [cancel] function that forces it to become _completed_ immediately.
 *
 * A job has two or three states:
 *
 * | **State**                        | [isActive] | [isCompleted] |
 * | -------------------------------- | ---------- | ------------- |
 * | _New_ (optional initial state)   | `false`    | `false`       |
 * | _Active_ (default initial state) | `true`     | `false`       |
 * | _Completed_ (final state)        | `false`    | `true`        |
 *
 * Usually, a job is created in _active_ state (it is created and started), so its only visible
 * states are _active_ and _completed_. However, coroutine builders that provide an optional `start` parameter
 * create a coroutine in _new_ state when this parameter is set to `false`. Such a job can
 * be made _active_ by invoking [start] or [join].
 *
 * A job in the coroutine [context][CoroutineScope.context] represents the coroutine itself.
 * A job is active while the coroutine is working and job's cancellation aborts the coroutine when
 * the coroutine is suspended on a _cancellable_ suspension point by throwing [CancellationException]
 * or the cancellation cause inside the coroutine.
 *
 * A job can have a _parent_. A job with a parent is cancelled when its parent completes.
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
         */
        public operator fun invoke(parent: Job? = null): Job = JobImpl(parent)
    }

    /**
     * Returns `true` when this job is active.
     */
    public val isActive: Boolean

    /**
     * Returns `true` when this job has completed for any reason.
     */
    public val isCompleted: Boolean

    /**
     * Starts coroutine related to this job (if any) if it was not started yet.
     * The result `true` if this invocation actually started coroutine or `false`
     * if it was already started or completed.
     */
    public fun start(): Boolean

    /**
     * Returns the exception that signals the completion of this job -- it returns the original
     * [cancel] cause or an instance of [CancellationException] if this job had completed
     * normally or was cancelled without a cause. This function throws
     * [IllegalStateException] when invoked for an job that has not [completed][isCompleted] yet.
     *
     * The [cancellable][suspendCancellableCoroutine] suspending functions throw this exception
     * when trying to suspend in the context of this job.
     */
    fun getCompletionException(): Throwable

    /**
     * Registers handler that is **synchronously** invoked on completion of this job.
     * When job is already complete, then the handler is immediately invoked
     * with a cancellation cause or `null`. Otherwise, handler will be invoked once when this
     * job is complete. Note, that [cancellation][cancel] is also a form of completion).
     *
     * The resulting [Registration] can be used to [Registration.unregister] if this
     * registration is no longer needed. There is no need to unregister after completion.
     */
    public fun invokeOnCompletion(handler: CompletionHandler): Registration

    /**
     * @suppress **Deprecated**: Renamed to `invokeOnCompletion`
     */
    @Deprecated(message = "Renamed to `invokeOnCompletion`", replaceWith = ReplaceWith("invokeOnCompletion"))
    public fun onCompletion(handler: CompletionHandler): Registration

    /**
     * Suspends coroutine until this job is complete. This invocation resumes normally (without exception)
     * when the job is complete for any reason. This function also [starts][Job.start] the corresponding coroutine
     * if the [Job] was still in _new_ state.
     *
     * This suspending function is cancellable. If the [Job] of the invoking coroutine is completed while this
     * suspending function is suspended, this function immediately resumes with [CancellationException].
     */
    public suspend fun join()

    /**
     * Cancel this activity with an optional cancellation [cause]. The result is `true` if this job was
     * cancelled as a result of this invocation and `false` otherwise
     * (if it was already _completed_ or if it is [NonCancellable]).
     * Repeated invocations of this function have no effect and always produce `false`.
     *
     * When cancellation has a clear reason in the code, an instance of [CancellationException] should be created
     * at the corresponding original cancellation site and passed into this method to aid in debugging by providing
     * both the context of cancellation and text description of the reason.
     */
    public fun cancel(cause: Throwable? = null): Boolean

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
     */
    public interface Registration {
        /**
         * Unregisters completion handler.
         */
        public fun unregister()
    }
}

/**
 * Handler for [Job.invokeOnCompletion].
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
 */
public fun Job.unregisterOnCompletion(registration: Job.Registration): Job.Registration =
    invokeOnCompletion(UnregisterOnCompletion(this, registration))

/**
 * Cancels a specified [future] when this job is complete.
 *
 * This is a shortcut for the following code with slightly more efficient implementation (one fewer object created).
 * ```
 * invokeOnCompletion { future.cancel(false) }
 * ```
 */
public fun Job.cancelFutureOnCompletion(future: Future<*>): Job.Registration =
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
public object EmptyRegistration : Job.Registration {
    /** Does not do anything. */
    override fun unregister() {}

    /** Returns "EmptyRegistration" string. */
    override fun toString(): String = "EmptyRegistration"
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
       EMPTY_N    EmptyNew     : New           no completion listeners
       EMPTY_A    EmptyActive  : Active        no completion listeners
       SINGLE     JobNode      : Active        a single completion listener
       SINGLE+    JobNode      : Active        a single completion listener + NodeList added as its next
       LIST_N     NodeList     : New           a list of listeners (promoted once, does not got back to EmptyNew)
       LIST_A     NodeList     : Active        a list of listeners (promoted once, does not got back to JobNode/EmptyActive)
       FINAL_C    Cancelled    : Completed     cancelled (final state)
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
          +---------+       +---------+

       This state machine and its transition matrix are optimized for the common case when job is created in active
       state (EMPTY_A) and at most one completion listener is added to it during its life-time.

       Note, that the actual `_state` variable can also be a reference to atomic operation descriptor `OpDescriptor`
     */

    @Volatile
    private var _state: Any? = if (active) EmptyActive else EmptyNew // shared objects while we have no listeners

    @Volatile
    private var registration: Job.Registration? = null

    protected companion object {
        @JvmStatic
        private val STATE: AtomicReferenceFieldUpdater<JobSupport, Any?> =
            AtomicReferenceFieldUpdater.newUpdater(JobSupport::class.java, Any::class.java, "_state")

        fun stateToString(state: Any?): String =
                if (state is Incomplete)
                    if (state.isActive) "Active" else "New"
                else "Completed"
    }

    /**
     * Initializes parent job.
     * It shall be invoked at most once after construction after all other initialization.
     */
    public fun initParentJob(parent: Job?) {
        check(registration == null)
        if (parent == null) {
            registration = EmptyRegistration
            return
        }
        // directly pass HandlerNode to parent scope to optimize one closure object (see makeNode)
        val newRegistration = parent.invokeOnCompletion(CancelOnCompletion(parent, this))
        registration = newRegistration
        // now check our state _after_ registering (see updateState order of actions)
        if (isCompleted) newRegistration.unregister()
    }

    /**
     * Returns current state of this job.
     */
    protected val state: Any? get() {
        while (true) { // lock-free helping loop
            val state = _state
            if (state !is OpDescriptor) return state
            state.perform(this)
        }
    }

    /**
     * Tries to update current [state] of this job.
     */
    internal fun updateState(expect: Any, update: Any?): Boolean {
        if (!tryUpdateState(expect, update)) return false
        completeUpdateState(expect, update)
        return true
    }

    internal fun tryUpdateState(expect: Any, update: Any?): Boolean  {
        require(expect is Incomplete && update !is Incomplete) // only incomplete -> completed transition is allowed
        if (!STATE.compareAndSet(this, expect, update)) return false
        // Unregister from parent job
        registration?.unregister() // volatile read registration _after_ state was updated
        return true // continues in completeUpdateState
    }

    internal fun completeUpdateState(expect: Any, update: Any?) {
        // Invoke completion handlers
        val cause = (update as? CompletedExceptionally)?.cause
        var completionException: Throwable? = null
        when (expect) {
            // SINGLE/SINGLE+ state -- one completion handler (common case)
            is JobNode<*> -> try {
                expect.invoke(cause)
            } catch (ex: Throwable) {
                completionException = ex
            }
            // LIST state -- a list of completion handlers
            is NodeList -> expect.forEach<JobNode<*>> { node ->
                try {
                    node.invoke(cause)
                } catch (ex: Throwable) {
                    completionException?.apply { addSuppressed(ex) } ?: run { completionException = ex }
                }

            }
            // otherwise -- do nothing (it was Empty*)
            else -> check(expect is Empty)
        }
        // handle invokeOnCompletion exceptions
        completionException?.let { handleCompletionException(it) }
        // Do other (overridable) processing after completion handlers
        afterCompletion(update)
    }

    public final override val isActive: Boolean get() {
        val state = this.state
        return state is Incomplete && state.isActive
    }

    public final override val isCompleted: Boolean get() = state !is Incomplete

    // this is for `select` operator. `isSelected` state means "not new" (== was started or already completed)
    public val isSelected: Boolean get() {
        val state = this.state
        return state !is Incomplete || state.isActive
    }

    public final override fun start(): Boolean {
        while (true) { // lock-free loop on state
            when (startInternal(state)) {
                0 -> return false
                1 -> return true
            }
        }
    }

    // return: 0 -> false (not new), 1 -> true (started), -1 -> retry
    internal fun startInternal(state: Any?): Int {
        when {
            // EMPTY_NEW state -- no completion handlers, new
            state === EmptyNew -> {
                if (!STATE.compareAndSet(this, state, EmptyActive)) return -1
                onStart()
                return 1
            }
            // LIST -- a list of completion handlers (either new or active)
            state is NodeList -> {
                if (state.isActive) return 0
                if (!NodeList.ACTIVE.compareAndSet(state, null, NodeList.ACTIVE_STATE)) return -1
                onStart()
                return 1
            }
            // not a new state
            else -> return 0
        }
    }

    internal fun describeStart(failureMarker: Any): AtomicDesc =
        object : AtomicDesc() {
            override fun prepare(op: AtomicOp): Any? {
                while (true) { // lock-free loop on state
                    val state = this@JobSupport._state
                    when {
                        state === op -> return null // already in progress
                        state is OpDescriptor -> state.perform(this@JobSupport) // help
                        state === EmptyNew -> { // EMPTY_NEW state -- no completion handlers, new
                            if (STATE.compareAndSet(this@JobSupport, state, op)) return null // success
                        }
                        state is NodeList -> { // LIST -- a list of completion handlers (either new or active)
                            if (state.isActive) return failureMarker
                            if (NodeList.ACTIVE.compareAndSet(state, null, op)) return null // success
                        }
                        else -> return failureMarker // not a new state
                    }
                }
            }

            override fun complete(op: AtomicOp, failure: Any?) {
                val success = failure == null
                val state = this@JobSupport._state
                when {
                    state === op -> {
                        if (STATE.compareAndSet(this@JobSupport, op, if (success) EmptyActive else EmptyNew)) {
                            if (success) onStart()
                        }
                    }
                    state is NodeList -> { // LIST -- a list of completion handlers (either new or active)
                        if (state._active === op) {
                            if (NodeList.ACTIVE.compareAndSet(state, op, if (success) NodeList.ACTIVE_STATE else null)) {
                                if (success) onStart()
                            }
                        }
                    }
                }
            }
        }

    /**
     * Override to provide the actual [start] action.
     */
    protected open fun onStart() {}

    final override fun getCompletionException(): Throwable {
        val state = this.state
        return when (state) {
            is Incomplete -> throw IllegalStateException("Job has not completed yet")
            is CompletedExceptionally -> state.exception
            else -> CancellationException("Job has completed normally")
        }
    }

    override fun onCompletion(handler: CompletionHandler): Job.Registration = invokeOnCompletion(handler)

    final override fun invokeOnCompletion(handler: CompletionHandler): Job.Registration {
        var nodeCache: JobNode<*>? = null
        while (true) { // lock-free loop on state
            val state = this.state
            when {
                // EMPTY_ACTIVE state -- no completion handlers, active
                state === EmptyActive -> {
                    // try move to SINGLE state
                    val node = nodeCache ?: makeNode(handler).also { nodeCache = it }
                    if (STATE.compareAndSet(this, state, node)) return node
                }
                // EMPTY_NEW state -- no completion handlers, new
                state === EmptyNew -> {
                    // try to promote it to list in new state
                    STATE.compareAndSet(this, state, NodeList(active = false))
                }
                // SINGLE/SINGLE+ state -- one completion handler
                state is JobNode<*> -> {
                    // try to promote it to list (SINGLE+ state)
                    state.addOneIfEmpty(NodeList(active = true))
                    // it must be in SINGLE+ state or state has changed (node could have need removed from state)
                    val list = state.next // either NodeList or somebody else won the race, updated state
                    // just attempt converting it to list if state is still the same, then continue lock-free loop
                    STATE.compareAndSet(this, state, list)
                }
                // LIST -- a list of completion handlers (either new or active)
                state is NodeList -> {
                    val node = nodeCache ?: makeNode(handler).also { nodeCache = it }
                    if (state.addLastIf(node) { this.state === state }) return node
                }
                // is inactive
                else -> {
                    handler((state as? CompletedExceptionally)?.exception)
                    return EmptyRegistration
                }
            }
        }
    }

    final override suspend fun join() {
        while (true) { // lock-free loop on state
            val state = this.state as? Incomplete ?: return // fast-path - no need to wait
            if (startInternal(state) >= 0) break // break unless needs to retry
        }
        return joinSuspend() // slow-path
    }

    private suspend fun joinSuspend() = suspendCancellableCoroutine<Unit> { cont ->
        cont.unregisterOnCompletion(invokeOnCompletion(ResumeOnCompletion(this, cont)))
    }

    internal fun removeNode(node: JobNode<*>) {
        // remove logic depends on the state of the job
        while (true) { // lock-free loop on job state
            val state = this.state
            when (state) {
                // SINGE/SINGLE+ state -- one completion handler
                is JobNode<*> -> {
                    if (state !== this) return // a different job node --> we were already removed
                    // try remove and revert back to empty state
                    if (STATE.compareAndSet(this, state, EmptyActive)) return
                }
                // LIST -- a list of completion handlers
                is NodeList -> {
                    // remove node from the list
                    node.remove()
                    return
                }
                // it is inactive or Empty* (does not have any completion handlers)
                else -> return
            }
        }
    }

    final override fun cancel(cause: Throwable?): Boolean {
        while (true) { // lock-free loop on state
            val state = this.state as? Incomplete ?: return false // quit if already complete
            if (updateState(state, Cancelled(cause))) return true
        }
    }

    /**
     * Override to process any exceptions that were encountered while invoking [invokeOnCompletion] handlers.
     */
    protected open fun handleCompletionException(closeException: Throwable) {
        throw closeException
    }

    /**
     * Override for post-completion actions that need to do something with the state.
     */
    protected open fun afterCompletion(state: Any?) {}

    private fun makeNode(handler: CompletionHandler): JobNode<*> =
            (handler as? JobNode<*>)?.also { require(it.job === this) }
                    ?: InvokeOnCompletion(this, handler)

    // for nicer debugging
    override fun toString(): String = "${this::class.java.simpleName}{${stateToString(state)}}@${Integer.toHexString(System.identityHashCode(this))}"

    /**
     * Interface for incomplete [state] of a job.
     */
    public interface Incomplete {
        val isActive: Boolean
    }

    private class NodeList(
        active: Boolean
    ) : LockFreeLinkedListHead(), Incomplete {
        @Volatile
        var _active: Any? = if (active) ACTIVE_STATE else null

        override val isActive: Boolean get() {
            while (true) { // helper loop for atomic ops
                val active = this._active
                if (active !is OpDescriptor) return active != null
                active.perform(this)
            }
        }

        companion object {
            @JvmStatic
            val ACTIVE: AtomicReferenceFieldUpdater<NodeList, Any?> =
                    AtomicReferenceFieldUpdater.newUpdater(NodeList::class.java, Any::class.java, "_active")

            @JvmStatic
            val ACTIVE_STATE = Symbol("ACTIVE_STATE")
        }

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
    public open class CompletedExceptionally(val cause: Throwable?) {
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
    public class Cancelled(cause: Throwable?) : CompletedExceptionally(cause)
}

private val EmptyNew = Empty(false)
private val EmptyActive = Empty(true)

private class Empty(override val isActive: Boolean) : JobSupport.Incomplete {
    override fun toString(): String = "Empty{${if (isActive) "Active" else "New" }}"
}

internal abstract class JobNode<out J : Job>(
    val job: J
) : LockFreeLinkedListNode(), Job.Registration, CompletionHandler, JobSupport.Incomplete {
    final override val isActive: Boolean get() = true
    // if unregister is called on this instance, then Job was an instance of JobSupport that added this node it itself
    // directly without wrapping
    final override fun unregister() = (job as JobSupport).removeNode(this)
    override abstract fun invoke(reason: Throwable?)
}

private class InvokeOnCompletion(
    job: Job,
    val handler: CompletionHandler
) : JobNode<Job>(job)  {
    override fun invoke(reason: Throwable?) = handler.invoke(reason)
    override fun toString() = "InvokeOnCompletion[${handler::class.java.name}@${Integer.toHexString(System.identityHashCode(handler))}]"
}

private class ResumeOnCompletion(
    job: Job,
    val continuation: Continuation<Unit>
) : JobNode<Job>(job)  {
    override fun invoke(reason: Throwable?) = continuation.resume(Unit)
    override fun toString() = "ResumeOnCompletion[$continuation]"
}

private class UnregisterOnCompletion(
    job: Job,
    val registration: Job.Registration
) : JobNode<Job>(job) {
    override fun invoke(reason: Throwable?) = registration.unregister()
    override fun toString(): String = "UnregisterOnCompletion[$registration]"
}

private class CancelOnCompletion(
    parentJob: Job,
    val subordinateJob: Job
) : JobNode<Job>(parentJob) {
    override fun invoke(reason: Throwable?) { subordinateJob.cancel(reason) }
    override fun toString(): String = "CancelOnCompletion[$subordinateJob]"
}

private class CancelFutureOnCompletion(
    job: Job,
    val future: Future<*>
) : JobNode<Job>(job)  {
    override fun invoke(reason: Throwable?) {
        // Don't interrupt when cancelling future on completion, because no one is going to reset this
        // interruption flag and it will cause spurious failures elsewhere
        future.cancel(false)
    }
    override fun toString() = "CancelFutureOnCompletion[$future]"
}

private class JobImpl(parent: Job? = null) : JobSupport(true) {
    init { initParentJob(parent) }
}