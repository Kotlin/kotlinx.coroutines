package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.internal.LinkedListHead
import kotlinx.coroutines.experimental.internal.LinkedListNode
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.buildSequence
import kotlin.coroutines.experimental.intrinsics.suspendCoroutineOrReturn

/**
 * A background job. Conceptually, a job is a cancellable thing with a simple life-cycle that
 * culminates in its completion. Jobs can be arranged into parent-child hierarchies where cancellation
 * or completion of parent immediately cancels all its [children].
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
 * | _Completing_ (optional transient state) | `true`     | `false`       | `false`       |
 * | _Cancelling_ (optional transient state) | `false`    | `false`       | `true`        |
 * | _Cancelled_ (final state)               | `false`    | `true`        | `true`        |
 * | _Completed_ (final state)               | `false`    | `true`        | `false`       |
 *
 * Usually, a job is created in _active_ state (it is created and started). However, coroutine builders
 * that provide an optional `start` parameter create a coroutine in _new_ state when this parameter is set to
 * [CoroutineStart.LAZY]. Such a job can be made _active_ by invoking [start] or [join].
 *
 * A job can be _cancelled_ at any time with [cancel] function that forces it to transition to
 * _cancelling_ state immediately. Job that is not backed by a coroutine and does not have
 * [children] becomes _cancelled_ on [cancel] immediately.
 * Otherwise, job becomes _cancelled_  when it finishes executing its code and
 * when all its children [complete][isCompleted].
 *
 * ```
 *                                                      wait children
 *    +-----+       start      +--------+   complete   +-------------+  finish  +-----------+
 *    | New | ---------------> | Active | -----------> | Completing  | -------> | Completed |
 *    +-----+                  +--------+              +-------------+          +-----------+
 *       |                         |                         |
 *       | cancel                  | cancel                  | cancel
 *       V                         V                         |
 *  +-----------+   finish   +------------+                  |
 *  | Cancelled | <--------- | Cancelling | <----------------+
 *  |(completed)|            +------------+
 *  +-----------+
 * ```
 *
 * A job in the [coroutineContext][CoroutineScope.coroutineContext] represents the coroutine itself.
 * A job is active while the coroutine is working and job's cancellation aborts the coroutine when
 * the coroutine is suspended on a _cancellable_ suspension point by throwing [CancellationException].
 *
 * A job can have a _parent_ job. A job with a parent is cancelled when its parent is cancelled or completes exceptionally.
 * Parent job waits for all its children to complete in _completing_ or _cancelling_ state.
 * _Completing_ state is purely internal to the job. For an outside observer a _completing_ job is still active,
 * while internally it is waiting for its children.
 *
 * All functions on this interface and on all interfaces derived from it are **thread-safe** and can
 * be safely invoked from concurrent coroutines without external synchronization.
 */
public actual interface Job : CoroutineContext.Element {

    // ------------ state query ------------

    /**
     * Returns `true` when this job is active -- it was already started and has not completed or cancelled yet.
     * The job that is waiting for its [children] to complete is still considered to be active if it
     * was not cancelled.
     */
    public actual val isActive: Boolean

    /**
     * Returns `true` when this job has completed for any reason. A job that was cancelled and has
     * finished its execution is also considered complete. Job becomes complete only after
     * all its [children] complete.
     */
    public actual val isCompleted: Boolean

    /**
     * Returns `true` if this job was [cancelled][cancel]. In the general case, it does not imply that the
     * job has already [completed][isCompleted] (it may still be cancelling whatever it was doing).
     */
    public actual val isCancelled: Boolean

    /**
     * Returns [CancellationException] that signals the completion of this job. This function is
     * used by [cancellable][suspendCancellableCoroutine] suspending functions. They throw exception
     * returned by this function when they suspend in the context of this job and this job becomes _complete_.
     *
     * This function returns the original [cancel] cause of this job if that `cause` was an instance of
     * [CancellationException]. Otherwise (if this job was cancelled with a cause of a different type, or
     * was cancelled without a cause, or had completed normally), an instance of [JobCancellationException] is
     * returned. The [JobCancellationException.cause] of the resulting [JobCancellationException] references
     * the original cancellation cause that was passed to [cancel] function.
     *
     * This function throws [IllegalStateException] when invoked on a job that has not
     * [completed][isCompleted] nor [cancelled][isCancelled] yet.
     */
    public actual fun getCancellationException(): CancellationException

    // ------------ state update ------------

    /**
     * Starts coroutine related to this job (if any) if it was not started yet.
     * The result `true` if this invocation actually started coroutine or `false`
     * if it was already started or completed.
     */
    public actual fun start(): Boolean

    /**
     * Cancels this job with an optional cancellation [cause]. The result is `true` if this job was
     * cancelled as a result of this invocation and `false` otherwise
     * (if it was already _completed_ or if it is [NonCancellable]).
     * Repeated invocations of this function have no effect and always produce `false`.
     *
     * When cancellation has a clear reason in the code, an instance of [CancellationException] should be created
     * at the corresponding original cancellation site and passed into this method to aid in debugging by providing
     * both the context of cancellation and text description of the reason.
     */
    public actual fun cancel(cause: Throwable? = null): Boolean

    // ------------ parent-child ------------

    /**
     * Returns a sequence of this job's children.
     *
     * A job becomes a child of this job when it is constructed with this job in its
     * [CoroutineContext] or using an explicit `parent` parameter.
     *
     * A parent-child relation has the following effect:
     *
     * * Cancellation of parent with [cancel] or its exceptional completion (failure)
     *   immediately cancels all its children.
     * * Parent cannot complete until all its children are complete. Parent waits for all its children to
     *   complete in _completing_ or _cancelling_ state.
     * * Uncaught exception in a child, by default, cancels parent. In particular, this applies to
     *   children created with [launch] coroutine builder. Note, that [async] and other future-like
     *   coroutine builders do not have uncaught exceptions by definition, since all their exceptions are
     *   caught and are encapsulated in their result.
     */
    public actual val children: Sequence<Job>

    /**
     * Attaches child job so that this job becomes its parent and
     * returns a handle that should be used to detach it.
     *
     * A parent-child relation has the following effect:
     * * Cancellation of parent with [cancel] or its exceptional completion (failure)
     *   immediately cancels all its children.
     * * Parent cannot complete until all its children are complete. Parent waits for all its children to
     *   complete in _completing_ or _cancelling_ state.
     *
     * **A child must store the resulting [DisposableHandle] and [dispose][DisposableHandle.dispose] the attachment
     * to its parent on its own completion.**
     *
     * Coroutine builders and job factory functions that accept `parent` [CoroutineContext] parameter
     * lookup a [Job] instance in the parent context and use this function to attach themselves as a child.
     * They also store a reference to the resulting [DisposableHandle] and dispose a handle when they complete.
     *
     * @suppress This is an internal API. This method is too error prone for public API.
     */
    @Deprecated(message = "Start child coroutine with 'parent' parameter", level = DeprecationLevel.WARNING)
    public actual fun attachChild(child: Job): DisposableHandle

    // ------------ state waiting ------------

    /**
     * Suspends coroutine until this job is complete. This invocation resumes normally (without exception)
     * when the job is complete for any reason and the [Job] of the invoking coroutine is still [active][isActive].
     * This function also [starts][Job.start] the corresponding coroutine if the [Job] was still in _new_ state.
     *
     * Note, that the job becomes complete only when all its children are complete.
     *
     * This suspending function is cancellable and **always** checks for the cancellation of invoking coroutine's Job.
     * If the [Job] of the invoking coroutine is cancelled or completed when this
     * suspending function is invoked or while it is suspended, this function
     * throws [CancellationException].
     *
     * In particular, it means that a parent coroutine invoking `join` on a child coroutine that was started using
     * `launch(coroutineContext) { ... }` builder throws [CancellationException] if the child
     * had crashed, unless a non-standard [CoroutineExceptionHandler] if installed in the context.
     *
     * There is [cancelAndJoin] function that combines an invocation of [cancel] and `join`.
     */
    public actual suspend fun join()

    // ------------ low-level state-notification ------------

    /**
     * Registers handler that is **synchronously** invoked once on cancellation or completion of this job.
     * When job is already cancelling or complete, then the handler is immediately invoked
     * with a job's cancellation cause or `null` unless [invokeImmediately] is set to false.
     * Otherwise, handler will be invoked once when this job is cancelled or complete.
     *
     * Invocation of this handler on a transition to a transient _cancelling_ state
     * is controlled by [onCancelling] boolean parameter.
     * The handler is invoked on invocation of [cancel] when
     * job becomes _cancelling_ if [onCancelling] parameter is set to `true`. However,
     * when this [Job] is not backed by a coroutine, like [CompletableDeferred] or [CancellableContinuation]
     * (both of which do not posses a _cancelling_ state), then the value of [onCancelling] parameter is ignored.
     *
     * The resulting [DisposableHandle] can be used to [dispose][DisposableHandle.dispose] the
     * registration of this handler and release its memory if its invocation is no longer needed.
     * There is no need to dispose the handler after completion of this job. The references to
     * all the handlers are released when this job completes.
     *
     * Installed [handler] should not throw any exceptions. If it does, they will get caught,
     * wrapped into [CompletionHandlerException], and rethrown, potentially causing crash of unrelated code.
     *
     * **Note**: This function is a part of internal machinery that supports parent-child hierarchies
     * and allows for implementation of suspending functions that wait on the Job's state.
     * This function should not be used in general application code.
     * Implementations of `CompletionHandler` must be fast and _lock-free_.
     *
     * @param onCancelling when `true`, then the [handler] is invoked as soon as this job transitions to _cancelling_ state;
     *        when `false` then the [handler] is invoked only when it transitions to _completed_ state.
     * @param invokeImmediately when `true` and this job is already in the desired state (depending on [onCancelling]),
     *        then the [handler] is immediately and synchronously invoked and [NonDisposableHandle] is returned;
     *        when `false` then [NonDisposableHandle] is returned, but the [handler] is not invoked.
     * @param handler the handler.
     */
    public actual fun invokeOnCompletion(
        onCancelling: Boolean = false,
        invokeImmediately: Boolean = true,
        handler: CompletionHandler): DisposableHandle

    /**
     * Key for [Job] instance in the coroutine context.
     */
    public actual companion object Key : CoroutineContext.Key<Job>
}

/**
 * Creates a new job object in an _active_ state.
 * It is optionally a child of a [parent] job.
 */
@Suppress("FunctionName")
public actual fun Job(parent: Job? = null): Job = JobImpl(parent)

/**
 * A handle to an allocated object that can be disposed to make it eligible for garbage collection.
 */
public actual interface DisposableHandle {
    /**
     * Disposes the corresponding object, making it eligible for garbage collection.
     * Repeated invocation of this function has no effect.
     */
    public actual fun dispose()
}

/**
 * This exception gets thrown if an exception is caught while processing [CompletionHandler] invocation for [Job].
 */
public actual class CompletionHandlerException public actual constructor(
    message: String,
    public override val cause: Throwable
) : RuntimeException(message.withCause(cause))

public actual open class CancellationException actual constructor(message: String) : IllegalStateException(message)

/**
 * Thrown by cancellable suspending functions if the [Job] of the coroutine is cancelled or completed
 * without cause, or with a cause or exception that is not [CancellationException]
 * (see [Job.getCancellationException]).
 */
public actual class JobCancellationException public actual constructor(
    message: String,
    public override val cause: Throwable?,
    /**
     * The job that was cancelled.
     */
    public actual val job: Job
) : CancellationException(message.withCause(cause)) {
    override fun toString(): String = "${super.toString()}; job=$job"
    override fun equals(other: Any?): Boolean =
            other === this ||
                    other is JobCancellationException && other.message == message && other.job == job && other.cause == cause
    override fun hashCode(): Int =
            (message!!.hashCode() * 31 + job.hashCode()) * 31 + (cause?.hashCode() ?: 0)
}

@Suppress("FunctionName")
private fun IllegalStateException(message: String, cause: Throwable?) =
    IllegalStateException(message.withCause(cause))

private fun String.withCause(cause: Throwable?) =
    if (cause == null) this else "$this; caused by $cause"

// -------------------- Job extensions --------------------

/**
 * Disposes a specified [handle] when this job is complete.
 *
 * This is a shortcut for the following code:
 * ```
 * invokeOnCompletion { handle.dispose() }
 * ```
 */
public actual fun Job.disposeOnCompletion(handle: DisposableHandle): DisposableHandle =
    invokeOnCompletion { handle.dispose() }

/**
 * Cancels the job and suspends invoking coroutine until the cancelled job is complete.
 *
 * This suspending function is cancellable and **always** checks for the cancellation of invoking coroutine's Job.
 * If the [Job] of the invoking coroutine is cancelled or completed when this
 * suspending function is invoked or while it is suspended, this function
 * throws [CancellationException].
 *
 * In particular, it means that a parent coroutine invoking `cancelAndJoin` on a child coroutine that was started using
 * `launch(coroutineContext) { ... }` builder throws [CancellationException] if the child
 * had crashed, unless a non-standard [CoroutineExceptionHandler] if installed in the context.
 *
 * This is a shortcut for the invocation of [cancel][Job.cancel] followed by [join][Job.join].
 */
public actual suspend fun Job.cancelAndJoin() {
    cancel()
    return join()
}

/**
 * Cancels all [children][Job.children] jobs of this coroutine with the given [cause] using [Job.cancel]
 * for all of them. Unlike [Job.cancel] on this job as a whole, the state of this job itself is not affected.
 */
public actual fun Job.cancelChildren(cause: Throwable? = null) {
    children.forEach { it.cancel(cause) }
}

/**
 * Suspends coroutine until all [children][Job.children] of this job are complete using
 * [Job.join] for all of them. Unlike [Job.join] on this job as a whole, it does not wait until
 * this job is complete.
 */
public actual suspend fun Job.joinChildren() {
    children.forEach { it.join() }
}

/**
 * No-op implementation of [DisposableHandle].
 */
public actual object NonDisposableHandle : DisposableHandle {
    /** Does not do anything. */
    actual override fun dispose() {}

    /** Returns "NonDisposableHandle" string. */
    override fun toString(): String = "NonDisposableHandle"
}

// --------------- helper classes to simplify job implementation


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
public open class JobSupport(active: Boolean) : Job {
    override val key: CoroutineContext.Key<*> get() = Job

    // Note: use shared objects while we have no listeners
    protected var state: Any? = if (active) EmptyActive else EmptyNew
        private set

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
        @Suppress("DEPRECATION")
        val handle = parent.attachChild(this)
        parentHandle = handle
        // now check our state _after_ registering (see updateState order of actions)
        if (isCompleted) {
            handle.dispose()
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
    }

    // ------------ state query ------------

    public final override val isActive: Boolean get() {
        val state = this.state
        return state is Incomplete && state.isActive
    }

    public final override val isCompleted: Boolean get() = state !is Incomplete

    public final override val isCancelled: Boolean get() {
        val state = this.state
        return state is Cancelled || (state is Finishing && state.cancelled != null)
    }

    // ------------ state update ------------

    /**
     * Updates current [state] of this job.
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal fun updateState(proposedUpdate: Any?, mode: Int) {
        val state = this.state as Incomplete // current state must be incomplete
        val update = coerceProposedUpdate(state, proposedUpdate)
        tryUpdateState(update)
        completeUpdateState(state, update, mode)
    }

    internal fun tryUpdateState(update: Any?) {
        require(update !is Incomplete) // only incomplete -> completed transition is allowed
        this.state = update
        // Unregister from parent job
        parentHandle?.let {
            it.dispose()
            parentHandle = NonDisposableHandle // release it just in case, to aid GC
        }
    }

    // when Job is in Cancelling state, it can only be promoted to Cancelled state,
    // so if the proposed Update is not an appropriate Cancelled (preserving the cancellation cause),
    // then the corresponding Cancelled state is constructed.
    private fun coerceProposedUpdate(expect: Incomplete, proposedUpdate: Any?): Any? =
        if (expect is Finishing && expect.cancelled != null && !isCorrespondinglyCancelled(expect.cancelled, proposedUpdate))
            createCancelled(expect.cancelled, proposedUpdate) else proposedUpdate

    private fun isCorrespondinglyCancelled(cancelled: Cancelled, proposedUpdate: Any?): Boolean {
        if (proposedUpdate !is Cancelled) return false
        // NOTE: equality comparison of causes is performed here by design, see equals of JobCancellationException
        return proposedUpdate.cause == cancelled.cause ||
                proposedUpdate.cause is JobCancellationException && cancelled.cause == null
    }

    private fun createCancelled(cancelled: Cancelled, proposedUpdate: Any?): Cancelled {
        if (proposedUpdate !is CompletedExceptionally) return cancelled // not exception -- just use original cancelled
        val exception = proposedUpdate.exception
        if (cancelled.exception == exception) return cancelled // that is the cancelled we need already!
        //cancelled.cause?.let { exception.addSuppressed(it) }
        return Cancelled(this, exception)
    }

    /**
     * Completes update of the current [state] of this job.
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal fun completeUpdateState(expect: Incomplete, update: Any?, mode: Int) {
        // Invoke completion handlers
        val exceptionally = update as? CompletedExceptionally
        val cause = exceptionally?.cause
        if (expect is JobNode<*>) { // SINGLE/SINGLE+ state -- one completion handler (common case)
            try {
                expect.invoke(cause)
            } catch (ex: Throwable) {
                handleException(CompletionHandlerException("Exception in completion handler $expect for $this", ex))
            }
        } else {
            expect.list?.notifyCompletion(cause)
        }
        // Do overridable processing after completion handlers
        if (!expect.isCancelling) onCancellation(exceptionally) // only notify when was not cancelling before
        afterCompletion(update, mode)
    }

    private inline fun <reified T: JobNode<*>> notifyHandlers(list: NodeList, cause: Throwable?) {
        var exception: Throwable? = null
        list.forEach<T> { node ->
            try {
                node.invoke(cause)
            } catch (ex: Throwable) {
                exception?.apply { /* addSuppressed(ex) */ } ?: run {
                    exception =  CompletionHandlerException("Exception in completion handler $node for $this", ex)
                }
            }
        }
        exception?.let { handleException(it) }
    }

    private fun NodeList.notifyCompletion(cause: Throwable?) =
            notifyHandlers<JobNode<*>>(this, cause)

    private fun notifyCancellation(list: NodeList, cause: Throwable?) =
            notifyHandlers<JobCancellationNode<*>>(list, cause)

    public final override fun start(): Boolean {
        val state = this.state
        when (state) {
            is Empty -> { // EMPTY_X state -- no completion handlers
                if (state.isActive) return false // already active
                onStart()
                return true
            }
            is NodeList -> { // LIST -- a list of completion handlers (either new or active)
                return state.makeActive().also { result ->
                    if (result) onStart()
                }
            }
            else -> return false // not a new state
        }
    }

    /**
     * Override to provide the actual [start] action.
     */
    protected open fun onStart() {}

    public final override fun getCancellationException(): CancellationException {
        val state = this.state
        return when {
            state is Finishing && state.cancelled != null ->
                state.cancelled.exception.toCancellationException("Job is being cancelled")
            state is Incomplete ->
                error("Job was not completed or cancelled yet: $this")
            state is CompletedExceptionally ->
                state.exception.toCancellationException("Job has failed")
            else -> JobCancellationException("Job has completed normally", null, this)
        }
    }

    private fun Throwable.toCancellationException(message: String): CancellationException =
            this as? CancellationException ?: JobCancellationException(message, this, this@JobSupport)

    /**
     * Returns the cause that signals the completion of this job -- it returns the original
     * [cancel] cause or **`null` if this job had completed
     * normally or was cancelled without a cause**. This function throws
     * [IllegalStateException] when invoked for an job that has not [completed][isCompleted] nor
     * [isCancelled] yet.
     */
    protected fun getCompletionCause(): Throwable? {
        val state = this.state
        return when {
            state is Finishing && state.cancelled != null -> state.cancelled.cause
            state is Incomplete -> error("Job was not completed or cancelled yet")
            state is CompletedExceptionally -> state.cause
            else -> null
        }
    }

    public final override fun invokeOnCompletion(onCancelling: Boolean, invokeImmediately: Boolean, handler: CompletionHandler) =
        installNode(onCancelling, invokeImmediately, makeNode(handler, onCancelling))

    private fun installNode(
        onCancelling: Boolean,
        invokeImmediately: Boolean,
        node: JobNode<*>
    ): DisposableHandle {
        while (true) {
            val state = this.state
            when (state) {
                is Empty -> { // EMPTY_X state -- no completion handlers
                    if (state.isActive) {
                        // move to SINGLE state
                        this.state = node
                        return node
                    } else
                        promoteEmptyToNodeList(state) // that way we can add listener for non-active coroutine
                }
                is Incomplete -> {
                    val list = state.list
                    if (list == null) { // SINGLE/SINGLE+
                        promoteSingleToNodeList(state as JobNode<*>)
                    } else {
                        if (state is Finishing && state.cancelled != null && onCancelling) {
                            check(hasCancellingState) // cannot be in this state unless were support cancelling state
                            // installing cancellation handler on job that is being cancelled
                            if (invokeImmediately) node.invoke(state.cancelled.cause)
                            return NonDisposableHandle
                        }
                        list.addLast(node)
                        return node
                    }
                }
                else -> { // is complete
                    if (invokeImmediately) node.invoke((state as? CompletedExceptionally)?.cause)
                    return NonDisposableHandle
                }
            }
        }
    }

    private fun makeNode(handler: CompletionHandler, onCancelling: Boolean): JobNode<*> =
        if (onCancelling && hasCancellingState)
            InvokeOnCancellation(this, handler)
        else
            InvokeOnCompletion(this, handler)


    private fun promoteEmptyToNodeList(state: Empty) {
        check(state === this.state)
        // promote it to list in new state
        this.state = NodeList(state.isActive)
    }

    private fun promoteSingleToNodeList(state: JobNode<*>) {
        check(state === this.state)
        // promote it to list (SINGLE+ state)
        val list = NodeList(isActive = true)
        list.addLast(state)
        this.state = list
    }

    final override suspend fun join() {
        if (!joinInternal()) { // fast-path no wait
            return suspendCoroutineOrReturn { cont ->
                cont.context.checkCompletion()
                Unit // do not suspend
            }
        }
        return joinSuspend() // slow-path wait
    }

    private fun joinInternal(): Boolean {
        if (state !is Incomplete) return false // not active anymore (complete) -- no need to wait
        start()
        return true // wait
    }

    private suspend fun joinSuspend() = suspendCancellableCoroutine<Unit> { cont ->
        val handle = invokeOnCompletion { cont.resume(Unit) }
        cont.invokeOnCompletion { handle.dispose() }
    }

    internal fun removeNode(node: JobNode<*>) {
        // remove logic depends on the state of the job
        val state = this.state
        when (state) {
            is JobNode<*> -> { // SINGE/SINGLE+ state -- one completion handler
                if (state !== node) return // a different job node --> we were already removed
                // remove and revert back to empty state
                this.state = EmptyActive
            }
            is Incomplete -> { // may have a list of completion handlers
                // remove node from the list if there is a list
                if (state.list != null) node.remove()
            }
        }
    }

    protected open val hasCancellingState: Boolean get() = false

    public override fun cancel(cause: Throwable?): Boolean =
        if (hasCancellingState)
            makeCancelling(cause) else
            makeCancelled(cause)

    // we will be dispatching coroutine to process its cancellation exception, so there is no need for
    // an extra check for Job status in MODE_CANCELLABLE
    private fun updateStateCancelled(cause: Throwable?) =
        updateState(Cancelled(this, cause), mode = MODE_ATOMIC_DEFAULT)

    // transitions to Cancelled state
    private fun makeCancelled(cause: Throwable?): Boolean {
        if (state !is Incomplete) return false // quit if already complete
        updateStateCancelled(cause)
        return true
    }

    // transitions to Cancelling state
    private fun makeCancelling(cause: Throwable?): Boolean {
        while (true) {
            val state = this.state
            when (state) {
                is Empty -> { // EMPTY_X state -- no completion handlers
                    if (state.isActive) {
                        promoteEmptyToNodeList(state) // this way can wrap it into Cancelling on next pass
                    } else {
                        // cancelling a non-started coroutine makes it immediately cancelled
                        // (and we have no listeners to notify which makes it very simple)
                        updateStateCancelled(cause)
                        return true
                    }
                }
                is JobNode<*> -> { // SINGLE/SINGLE+ state -- one completion handler
                    promoteSingleToNodeList(state)
                }
                is NodeList -> { // LIST -- a list of completion handlers (either new or active)
                    if (state.isActive) {
                        makeCancellingList(state.list, cause)
                        return true
                    } else {
                        // cancelling a non-started coroutine makes it immediately cancelled
                        updateStateCancelled(cause)
                        return true
                    }
                }
                is Finishing -> { // Completing/Cancelling the job, may cancel
                    if (state.cancelled != null) return false // already cancelling
                    makeCancellingList(state.list, cause)
                    return true
                }
                else -> { // is inactive
                    return false
                }
            }
        }
    }

    // make expected state in cancelling
    private fun makeCancellingList(list: NodeList, cause: Throwable?) {
        val cancelled = Cancelled(this, cause)
        state = Finishing(list, cancelled, false)
        notifyCancellation(list, cause)
        onCancellation(cancelled)
    }

    /**
     * Returns:
     * * `true` if state was updated to completed/cancelled;
     * * `false` if made completing or it is cancelling and is waiting for children.
     *
     * @throws IllegalStateException if job is already complete or completing
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal fun makeCompleting(proposedUpdate: Any?, mode: Int): Boolean {
        loop@ while (true) {
            val state = this.state
            @Suppress("FoldInitializerAndIfToElvis")
            if (state !is Incomplete)
                throw IllegalStateException("Job $this is already complete, but is being completed with $proposedUpdate", proposedUpdate.exceptionOrNull)
            if (state is Finishing && state.completing)
                throw IllegalStateException("Job $this is already completing, but is being completed with $proposedUpdate", proposedUpdate.exceptionOrNull)
            val child: Child = firstChild(state) ?: run {
                // or else complete immediately w/o children
                updateState(proposedUpdate, mode)
                return true
            }
            // must promote to list to correct operate on child lists
            if (state is JobNode<*>) {
                promoteSingleToNodeList(state)
                continue@loop // retry
            }
            // cancel all children in list on exceptional completion
            if (proposedUpdate is CompletedExceptionally)
                child.cancelChildrenInternal(proposedUpdate.exception)
            // switch to completing state
            val completing = Finishing(state.list!!, (state as? Finishing)?.cancelled, true)
            this.state = completing
            if (tryWaitForChild(child, proposedUpdate))
                return false
            updateState(proposedUpdate, MODE_ATOMIC_DEFAULT)
            return true
        }
    }

    private tailrec fun Child.cancelChildrenInternal(cause: Throwable) {
        childJob.cancel(JobCancellationException("Child job was cancelled because of parent failure", cause, childJob))
        nextChild()?.cancelChildrenInternal(cause)
    }

    private val Any?.exceptionOrNull: Throwable?
        get() = (this as? CompletedExceptionally)?.exception

    private fun firstChild(state: Incomplete) =
        state as? Child ?: state.list?.nextChild()

    // return false when there is no more incomplete children to wait
    private tailrec fun tryWaitForChild(child: Child, proposedUpdate: Any?): Boolean {
        val handle = child.childJob.invokeOnCompletion(invokeImmediately = false) {
            continueCompleting(child, proposedUpdate)
        }
        if (handle !== NonDisposableHandle) return true // child is not complete and we've started waiting for it
        val nextChild = child.nextChild() ?: return false
        return tryWaitForChild(nextChild, proposedUpdate)
    }

    internal fun continueCompleting(lastChild: Child, proposedUpdate: Any?) {
        val state = this.state
        @Suppress("FoldInitializerAndIfToElvis")
        if (state !is Finishing)
            throw IllegalStateException("Job $this is found in expected state while completing with $proposedUpdate", proposedUpdate.exceptionOrNull)
        // figure out if we need to wait for next child
        val waitChild = lastChild.nextChild()
        // try wait for next child
        if (waitChild != null && tryWaitForChild(waitChild, proposedUpdate)) return // waiting for next child
        // no more children to wait -- update state
        updateState(proposedUpdate, MODE_ATOMIC_DEFAULT)
    }

    private fun LinkedListNode.nextChild(): Child? {
        var cur = this
        while (cur.isRemoved) cur = cur.prev // rollback to prev non-removed (or list head)
        while (true) {
            cur = cur.next
            if (cur is Child) return cur
            if (cur is NodeList) return null // checked all -- no more children
        }
    }

    override val children: Sequence<Job> get() = buildSequence<Job> {
        val state = this@JobSupport.state
        when (state) {
            is Child -> yield(state.childJob)
            is Incomplete -> state.list?.let { list ->
                list.forEach<Child> { yield(it.childJob) }
            }
        }
    }

    @Suppress("OverridingDeprecatedMember")
    override fun attachChild(child: Job): DisposableHandle =
        installNode(onCancelling = true, invokeImmediately = true, node = Child(this, child))

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
     * @param exceptionally not null when the the job was cancelled or completed exceptionally,
     *               null when it has completed normally.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun onCancellation(exceptionally: CompletedExceptionally?) {}

    /**
     * Override for post-completion actions that need to do something with the state.
     * @param mode completion mode.
     * @suppress **This is unstable API and it is subject to change.**
     */
    protected open fun afterCompletion(state: Any?, mode: Int) {}

    // for nicer debugging
    override fun toString(): String = "Job{${stateString()}}"

    protected fun stateString(): String {
        val state = this.state
        return when (state) {
            is Finishing -> buildString {
                if (state.cancelled != null) append("Cancelling")
                if (state.completing) append("Completing")
            }
            is Incomplete -> if (state.isActive) "Active" else "New"
            is Cancelled -> "Cancelled"
            is CompletedExceptionally -> "CompletedExceptionally"
            else -> "Completed"
        }
    }

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal interface Incomplete {
        val isActive: Boolean
        val list: NodeList? // is null only for Empty and JobNode incomplete state objects
    }

    // Cancelling or Completing
    private class Finishing(
        override val list: NodeList,
        val cancelled: Cancelled?, /* != null when cancelling */
        val completing: Boolean /* true when completing */
    ) : Incomplete {
        override val isActive: Boolean get() = cancelled == null
    }

    private val Incomplete.isCancelling: Boolean
        get() = this is Finishing && cancelled != null

    /**
     * @suppress **This is unstable API and it is subject to change.**
     */
    internal class NodeList(
        override var isActive: Boolean
    ) : LinkedListHead(), Incomplete {
        override val list: NodeList get() = this

        fun makeActive(): Boolean {
            if (isActive) return false
            isActive = true
            return true
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
     * @param cause the exceptional completion cause. If `cause` is null, then an exception is
     *        if created via [createException] on first get from [exception] property.
     * @param allowNullCause if `null` cause is allowed.
     */
    public open class CompletedExceptionally protected constructor(
        public val cause: Throwable?,
        allowNullCause: Boolean
    ) {
        /**
         * Creates exceptionally completed state.
         * @param cause the exceptional completion cause.
         */
        public constructor(cause: Throwable) : this(cause, false)

        private var _exception: Throwable? = cause // will materialize JobCancellationException on first need

        init {
            require(allowNullCause || cause != null) { "Null cause is not allowed" }
        }

        /**
         * Returns completion exception.
         */
        public val exception: Throwable get() =
            _exception ?: createException().also { _exception = it }

        protected open fun createException(): Throwable = error("Completion exception was not specified")
    }

    /**
     * A specific subclass of [CompletedExceptionally] for cancelled jobs.
     *
     * @param job the job that was cancelled.
     * @param cause the exceptional completion cause. If `cause` is null, then a [JobCancellationException]
     *        if created on first get from [exception] property.
     */
    public class Cancelled(
        private val job: Job,
        cause: Throwable?
    ) : CompletedExceptionally(cause, true) {
        override fun createException(): Throwable = JobCancellationException("Job was cancelled normally", null, job)
    }

    /*
     * =================================================================================================
     * This is ready-to-use implementation for Deferred interface.
     * However, it is not type-safe. Conceptually it just exposes the value of the underlying
     * completed state as `Any?`
     * =================================================================================================
     */

    public val isCompletedExceptionally: Boolean get() = state is CompletedExceptionally

    public fun getCompletionExceptionOrNull(): Throwable? {
        val state = this.state
        check(state !is Incomplete) { "This job has not completed yet" }
        return state.exceptionOrNull
    }

    protected fun getCompletedInternal(): Any? {
        val state = this.state
        check(state !is Incomplete) { "This job has not completed yet" }
        if (state is CompletedExceptionally) throw state.exception
        return state
    }

    protected suspend fun awaitInternal(): Any? {
        val state = this.state
        if (state !is Incomplete) {
            // already complete -- just return result
            if (state is CompletedExceptionally) throw state.exception
            return state
        }
        start()
        return awaitSuspend() // slow-path
    }

    private suspend fun awaitSuspend(): Any? = suspendCancellableCoroutine { cont ->
        val handle = invokeOnCompletion {
            val state = this.state
            check(state !is Incomplete)
            if (state is CompletedExceptionally)
                cont.resumeWithException(state.exception)
            else
                cont.resume(state)
        }
        cont.invokeOnCompletion { handle.dispose() }
    }
}

@Suppress("PrivatePropertyName")
private val EmptyNew = Empty(false)
@Suppress("PrivatePropertyName")
private val EmptyActive = Empty(true)

private class Empty(override val isActive: Boolean) : JobSupport.Incomplete {
    override val list: JobSupport.NodeList? get() = null
    override fun toString(): String = "Empty{${if (isActive) "Active" else "New" }}"
}

private class JobImpl(parent: Job? = null) : JobSupport(true) {
    init { initParentJob(parent) }
}

// -------- invokeOnCompletion nodes

internal abstract class JobNode<out J : Job>(
    val job: J
) : LinkedListNode(), DisposableHandle, JobSupport.Incomplete {
    final override val isActive: Boolean get() = true
    final override val list: JobSupport.NodeList? get() = null
    final override fun dispose() = (job as JobSupport).removeNode(this)
    abstract fun invoke(reason: Throwable?) // CompletionHandler -- invoked on completion
}

private class InvokeOnCompletion(
    job: Job,
    private val handler: CompletionHandler
) : JobNode<Job>(job)  {
    override fun invoke(reason: Throwable?) = handler.invoke(reason)
    override fun toString() = "InvokeOnCompletion"
}

// -------- invokeOnCancellation nodes

/**
 * Marker for node that shall be invoked on cancellation (in _cancelling_ state).
 * **Note: may be invoked multiple times during cancellation.**
 */
internal abstract class JobCancellationNode<out J : Job>(job: J) : JobNode<J>(job)

private class InvokeOnCancellation(
    job: Job,
    private val handler: CompletionHandler
) : JobCancellationNode<Job>(job)  {
    // delegate handler shall be invoked at most once, so here is an additional flag
    private var invoked = false
    override fun invoke(reason: Throwable?) {
        if (invoked) return
        invoked = true
        handler.invoke(reason)
    }
    override fun toString() = "InvokeOnCancellation"
}

internal class Child(
    parent: JobSupport,
    val childJob: Job
) : JobCancellationNode<JobSupport>(parent) {
    override fun invoke(reason: Throwable?) {
        // Always materialize the actual instance of parent's completion exception and cancel child with it
        childJob.cancel(job.getCancellationException())
    }
    override fun toString(): String = "Child[$childJob]"
}

