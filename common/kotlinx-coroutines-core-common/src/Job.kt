/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("JobKt")
@file:Suppress("DEPRECATION_ERROR", "RedundantUnitReturnType")

package kotlinx.coroutines

import kotlinx.coroutines.selects.*
import kotlin.coroutines.*
import kotlin.jvm.*

// --------------- core job interfaces ---------------

/**
 * A background job. Conceptually, a job is a cancellable thing with a life-cycle that
 * culminates in its completion.
 *
 * Jobs can be arranged into parent-child hierarchies where cancellation
 * of parent lead to an immediate cancellation of all its [children]. Failure or cancellation of a child
 * with an exception other than [CancellationException] immediately cancels its parent. This way, parent
 * can [cancel] its own children (including all their children recursively) without cancelling itself.
 *
 * The most basic instances of [Job] are created with [launch][CoroutineScope.launch] coroutine builder or with a
 * `Job()` factory function. By default, a failure of any of the job's children leads to an immediately failure
 * of its parent and cancellation of the rest of its children. This behavior can be customized using [SupervisorJob].
 *
 * Conceptually, an execution of the job does not produce a result value. Jobs are launched solely for their
 * side-effects. See [Deferred] interface for a job that produces a result.
 *
 * A job has the following states:
 *
 * | **State**                        | [isActive] | [isCompleted] | [isCancelled] |
 * | -------------------------------- | ---------- | ------------- | ------------- |
 * | _New_ (optional initial state)   | `false`    | `false`       | `false`       |
 * | _Active_ (default initial state) | `true`     | `false`       | `false`       |
 * | _Completing_ (transient state)   | `true`     | `false`       | `false`       |
 * | _Cancelling_ (transient state)   | `false`    | `false`       | `true`        |
 * | _Cancelled_ (final state)        | `false`    | `true`        | `true`        |
 * | _Completed_ (final state)        | `false`    | `true`        | `false`       |
 *
 * Usually, a job is created in _active_ state (it is created and started). However, coroutine builders
 * that provide an optional `start` parameter create a coroutine in _new_ state when this parameter is set to
 * [CoroutineStart.LAZY]. Such a job can be made _active_ by invoking [start] or [join].
 *
 * A job is _active_ while the coroutine is working. Failure of the job with exception makes it _cancelling_.
 * A job can be cancelled it at any time with [cancel] function that forces it to transition to
 * _cancelling_ state immediately. The job becomes _cancelled_  when it finishes executing it work.
 *
 * ```
 *                                       wait children
 * +-----+ start  +--------+ complete   +-------------+  finish  +-----------+
 * | New | -----> | Active | ---------> | Completing  | -------> | Completed |
 * +-----+        +--------+            +-------------+          +-----------+
 *                  |  cancel / fail       |
 *                  |     +----------------+
 *                  |     |
 *                  V     V
 *              +------------+                           finish  +-----------+
 *              | Cancelling | --------------------------------> | Cancelled |
 *              +------------+                                   +-----------+
 * ```
 *
 * A `Job` instance in the
 * [coroutineContext](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.coroutines/coroutine-context.html)
 * represents the coroutine itself.
 *
 * A job can have a _parent_ job. A job with a parent is cancelled when its parent is cancelled.
 * Parent job waits in _completing_ or _cancelling_ state for all its children to complete before finishing.
 * Note, that _completing_ state is purely internal to the job. For an outside observer a _completing_ job is still
 * active, while internally it is waiting for its children.
 *
 * Normal cancellation of a job is distinguished from its failure by the type of its cancellation exception cause.
 * If the cause of cancellation is [CancellationException], then the job is considered to be _cancelled normally_.
 * This usually happens when [cancel] is invoked without additional parameters. If the cause of cancellation is
 * a different exception, then the job is considered to have _failed_. This usually happens when the code of the job
 * encounters some problem and throws an exception.
 *
 * All functions on this interface and on all interfaces derived from it are **thread-safe** and can
 * be safely invoked from concurrent coroutines without external synchronization.
 */
public interface Job : CoroutineContext.Element {
    /**
     * Key for [Job] instance in the coroutine context.
     */
    public companion object Key : CoroutineContext.Key<Job> {
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
     * Returns `true` when this job is active -- it was already started and has not completed nor was cancelled yet.
     * The job that is waiting for its [children] to complete is still considered to be active if it
     * was not cancelled nor failed.
     *
     * See [Job] documentation for more details on job states.
     */
    public val isActive: Boolean

    /**
     * Returns `true` when this job has completed for any reason. A job that was cancelled or failed
     * and has finished its execution is also considered complete. Job becomes complete only after
     * all its [children] complete.
     *
     * See [Job] documentation for more details on job states.
     */
    public val isCompleted: Boolean

    /**
     * Returns `true` if this job was cancelled for any reason, either by explicit invocation of [cancel] or
     * because it had failed or its child or parent was cancelled.
     * In the general case, it does not imply that the
     * job has already [completed][isCompleted], because it may still be finishing whatever it was doing and
     * waiting for its [children] to complete.
     *
     * See [Job] documentation for more details on cancellation and failures.
     */
    public val isCancelled: Boolean

    /**
     * Returns [CancellationException] that signals the completion of this job. This function is
     * used by [cancellable][suspendCancellableCoroutine] suspending functions. They throw exception
     * returned by this function when they suspend in the context of this job and this job becomes _complete_.
     *
     * This function returns the original [cancel] cause of this job if that `cause` was an instance of
     * [CancellationException]. Otherwise (if this job was cancelled with a cause of a different type, or
     * was cancelled without a cause, or had completed normally), an instance of [CancellationException] is
     * returned. The [CancellationException.cause] of the resulting [CancellationException] references
     * the original cancellation cause that was passed to [cancel] function.
     *
     * This function throws [IllegalStateException] when invoked on a job that is still active.
     *
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    public fun getCancellationException(): CancellationException

    // ------------ state update ------------

    /**
     * Starts coroutine related to this job (if any) if it was not started yet.
     * The result `true` if this invocation actually started coroutine or `false`
     * if it was already started or completed.
     */
    public fun start(): Boolean

    /**
     * @suppress
     */
    @Suppress("INAPPLICABLE_JVM_NAME", "DEPRECATION")
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Left here for binary compatibility")
    @JvmName("cancel")
    public fun cancel0(): Boolean = cancel(null)

    /**
     * Cancels this job.
     * See [Job] documentation for full explanation of cancellation machinery.
     */
    public fun cancel(): Unit

    /**
     * @suppress
     */
    @ObsoleteCoroutinesApi
    @Deprecated(level = DeprecationLevel.WARNING, message = "Use CompletableDeferred.completeExceptionally(cause) or Job.cancel() instead",
        replaceWith = ReplaceWith("cancel()")
    )
    public fun cancel(cause: Throwable? = null): Boolean

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
     *   children created with [launch][CoroutineScope.launch] coroutine builder. Note, that
     *   [async][CoroutineScope.async] and other future-like
     *   coroutine builders do not have uncaught exceptions by definition, since all their exceptions are
     *   caught and are encapsulated in their result.
     */
    public val children: Sequence<Job>

    /**
     * Attaches child job so that this job becomes its parent and
     * returns a handle that should be used to detach it.
     *
     * A parent-child relation has the following effect:
     * * Cancellation of parent with [cancel] or its exceptional completion (failure)
     *   immediately cancels all its children.
     * * Parent cannot complete until all its children are complete. Parent waits for all its children to
     *   complete in _completing_ or _cancelling_ states.
     *
     * **A child must store the resulting [ChildHandle] and [dispose][DisposableHandle.dispose] the attachment
     * to its parent on its own completion.**
     *
     * Coroutine builders and job factory functions that accept `parent` [CoroutineContext] parameter
     * lookup a [Job] instance in the parent context and use this function to attach themselves as a child.
     * They also store a reference to the resulting [ChildHandle] and dispose a handle when they complete.
     *
     * @suppress This is an internal API. This method is too error prone for public API.
     */
    // ChildJob and ChildHandle are made internal on purpose to further deter 3rd-party impl of Job
    @InternalCoroutinesApi
    public fun attachChild(child: ChildJob): ChildHandle

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
     * This function can be used in [select] invocation with [onJoin] clause.
     * Use [isCompleted] to check for completion of this job without waiting.
     *
     * There is [cancelAndJoin] function that combines an invocation of [cancel] and `join`.
     */
    public suspend fun join()

    /**
     * Clause for [select] expression of [join] suspending function that selects when the job is complete.
     * This clause never fails, even if the job completes exceptionally.
     */
    public val onJoin: SelectClause0

    // ------------ low-level state-notification ------------

    /**
     * Registers handler that is **synchronously** invoked once on completion of this job.
     * When job is already complete, then the handler is immediately invoked
     * with a job's exception or cancellation cause or `null`. Otherwise, handler will be invoked once when this
     * job is complete.
     *
     * The meaning of `cause` that is passed to the handler:
     * * Cause is `null` when job has completed normally.
     * * Cause is an instance of [CancellationException] when job was cancelled _normally_.
     *   **It should not be treated as an error**. In particular, it should not be reported to error logs.
     * * Otherwise, the job had _failed_.
     *
     * The resulting [DisposableHandle] can be used to [dispose][DisposableHandle.dispose] the
     * registration of this handler and release its memory if its invocation is no longer needed.
     * There is no need to dispose the handler after completion of this job. The references to
     * all the handlers are released when this job completes.
     *
     * Installed [handler] should not throw any exceptions. If it does, they will get caught,
     * wrapped into [CompletionHandlerException], and rethrown, potentially causing crash of unrelated code.
     *
     * **Note**: Implementations of `CompletionHandler` must be fast and _lock-free_.
     */
    public fun invokeOnCompletion(handler: CompletionHandler): DisposableHandle

    /**
     * Registers handler that is **synchronously** invoked once on cancellation or completion of this job.
     * When job was already cancelled and is completed its execution, then the handler is immediately invoked
     * with a job's cancellation cause or `null` unless [invokeImmediately] is set to false.
     * Otherwise, handler will be invoked once when this job is cancelled or is complete.
     *
     * The meaning of `cause` that is passed to the handler:
     * * Cause is `null` when job has completed normally.
     * * Cause is an instance of [CancellationException] when job was cancelled _normally_.
     *   **It should not be treated as an error**. In particular, it should not be reported to error logs.
     * * Otherwise, the job had _failed_.
     *
     * Invocation of this handler on a transition to a _cancelling_ state
     * is controlled by [onCancelling] boolean parameter.
     * The handler is invoked when the job becomes _cancelling_ if [onCancelling] parameter is set to `true`.
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
     *        then the [handler] is immediately and synchronously invoked and no-op [DisposableHandle] is returned;
     *        when `false` then no-op [DisposableHandle] is returned, but the [handler] is not invoked.
     * @param handler the handler.
     *
     * @suppress **This an internal API and should not be used from general code.**
     */
    @InternalCoroutinesApi
    public fun invokeOnCompletion(
        onCancelling: Boolean = false,
        invokeImmediately: Boolean = true,
        handler: CompletionHandler): DisposableHandle

    // ------------ unstable internal API ------------

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
}

/**
 * Creates a new job object in an active state.
 * A failure of any child of this job immediately causes this job to fail, too, and cancels the rest of its children.
 *
 * To handle children failure independently of each other use [SupervisorJob].
 *
 * If [parent] job is specified, then this job becomes a child job of its parent and
 * is cancelled when its parent fails or is cancelled. All this job's children are cancelled in this case, too.
 * The invocation of [cancel][Job.cancel] with exception (other than [CancellationException]) on this job also cancels parent.
 *
 * @param parent an optional parent job.
 */
@Suppress("FunctionName")
public fun Job(parent: Job? = null): Job = JobImpl(parent)

/**
 * A handle to an allocated object that can be disposed to make it eligible for garbage collection.
 */
public interface DisposableHandle {
    /**
     * Disposes the corresponding object, making it eligible for garbage collection.
     * Repeated invocation of this function has no effect.
     */
    public fun dispose()
}

/**
 * @suppress **This an internal API and should not be used from general code.**
 */
@Suppress("FunctionName")
@InternalCoroutinesApi
public inline fun DisposableHandle(crossinline block: () -> Unit) =
    object : DisposableHandle {
        override fun dispose() {
            block()
        }
    }

// -------------------- Parent-child communication --------------------

/**
 * A reference that parent receives from its child so that it can report its cancellation.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@InternalCoroutinesApi
@Deprecated(level = DeprecationLevel.ERROR, message = "This is internal API and may be removed in the future releases")
public interface ChildJob : Job {
    /**
     * Parent is cancelling its child by invoking this method.
     * Child finds the cancellation cause using [ParentJob.getChildJobCancellationCause].
     * This method does nothing is the child is already being cancelled.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    @InternalCoroutinesApi
    public fun parentCancelled(parentJob: ParentJob)
}

/**
 * A reference that child receives from its parent when it is being cancelled by the parent.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@InternalCoroutinesApi
@Deprecated(level = DeprecationLevel.ERROR, message = "This is internal API and may be removed in the future releases")
public interface ParentJob : Job {
    /**
     * Child job is using this method to learn its cancellation cause when the parent cancels it with [ChildJob.parentCancelled].
     * This method is invoked only if the child was not already being cancelled.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    @InternalCoroutinesApi
    public fun getChildJobCancellationCause(): Throwable
}

/**
 * A handle that child keep onto its parent so that it is able to report its cancellation.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@InternalCoroutinesApi
@Deprecated(level = DeprecationLevel.ERROR, message = "This is internal API and may be removed in the future releases")
public interface ChildHandle : DisposableHandle {
    /**
     * Child is cancelling its parent by invoking this method.
     * This method is invoked by the child twice. The first time child report its root cause as soon as possible,
     * so that all its siblings and the parent can start cancelling their work asap. The second time
     * child invokes this method when it had aggregated and determined its final cancellation cause.
     *
     * @suppress **This is unstable API and it is subject to change.**
     */
    @InternalCoroutinesApi
    public fun childCancelled(cause: Throwable): Boolean
}

// -------------------- Job extensions --------------------

/**
 * Disposes a specified [handle] when this job is complete.
 *
 * This is a shortcut for the following code with slightly more efficient implementation (one fewer object created).
 * ```
 * invokeOnCompletion { handle.dispose() }
 * ```
 */
internal fun Job.disposeOnCompletion(handle: DisposableHandle): DisposableHandle =
    invokeOnCompletion(handler = DisposeOnCompletion(this, handle).asHandler)

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
 * had crashed, unless a non-standard [CoroutineExceptionHandler] is installed in the context.
 *
 * This is a shortcut for the invocation of [cancel][Job.cancel] followed by [join][Job.join].
 */
public suspend fun Job.cancelAndJoin() {
    cancel()
    return join()
}

/**
 * @suppress
 */
@ObsoleteCoroutinesApi
@Deprecated(level = DeprecationLevel.WARNING, message = "Use cancelChildren() without cause", replaceWith = ReplaceWith("cancelChildren()"))
public fun Job.cancelChildren(cause: Throwable? = null) {
    @Suppress("DEPRECATION")
    children.forEach { it.cancel(cause) }
}

/**
 * Cancels all [children][Job.children] jobs of this coroutine using [Job.cancel] for all of them.
 * Unlike [Job.cancel] on this job as a whole, the state of this job itself is not affected.
 */
public fun Job.cancelChildren() {
    children.forEach { it.cancel() }
}

// -------------------- CoroutineContext extensions --------------------

/**
 * Returns `true` when the [Job] of the coroutine in this context is still active
 * (has not completed and was not cancelled yet).
 *
 * Check this property in long-running computation loops to support cancellation
 * when [CoroutineScope.isActive] is not available:
 *
 * ```
 * while (coroutineContext.isActive) {
 *     // do some computation
 * }
 * ```
 *
 * The `coroutineContext.isActive` expression is a shortcut for `coroutineContext[Job]?.isActive == true`.
 * See [Job.isActive].
 */
public val CoroutineContext.isActive: Boolean
    get() = this[Job]?.isActive == true


/**
 * @suppress
 */
@Suppress("unused")
@JvmName("cancel")
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun CoroutineContext.cancel0(): Boolean {
    this[Job]?.cancel()
    return true
}

/**
 * Cancels [Job] of this context. See [Job.cancel] for details.
 */
public fun CoroutineContext.cancel(): Unit {
    this[Job]?.cancel()
}

/**
 * @suppress
 */
@ObsoleteCoroutinesApi
@Deprecated(level = DeprecationLevel.WARNING, message = "Use cancel() without cause", replaceWith = ReplaceWith("cancel()"))
public fun CoroutineContext.cancel(cause: Throwable? = null): Boolean =
    @Suppress("DEPRECATION")
    this[Job]?.cancel(cause) ?: false

/**
 * Cancels all children of the [Job] in this context, without touching the the state of this job itself.
 * It does not do anything if there is no job in the context or it has no children.
 */
public fun CoroutineContext.cancelChildren() {
    this[Job]?.children?.forEach { it.cancel() }
}

@ObsoleteCoroutinesApi
@Deprecated(level = DeprecationLevel.WARNING, message = "Use cancelChildren() without cause", replaceWith = ReplaceWith("cancelChildren()"))
public fun CoroutineContext.cancelChildren(cause: Throwable? = null) {
    @Suppress("DEPRECATION")
    this[Job]?.children?.forEach { it.cancel(cause) }
}

/**
 * No-op implementation of [DisposableHandle].
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public object NonDisposableHandle : DisposableHandle, ChildHandle {
    /**
     * Does not do anything.
     * @suppress
     */
    override fun dispose() {}

    /**
     * Returns `false`.
     * @suppress
     */
    override fun childCancelled(cause: Throwable): Boolean = false

    /**
     * Returns "NonDisposableHandle" string.
     * @suppress
     */
    override fun toString(): String = "NonDisposableHandle"
}
