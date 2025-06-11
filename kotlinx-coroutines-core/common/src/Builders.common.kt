@file:JvmMultifileClass
@file:JvmName("BuildersKt")
@file:OptIn(ExperimentalContracts::class)
@file:Suppress("LEAKED_IN_PLACE_LAMBDA", "WRONG_INVOCATION_KIND")

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.selects.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.jvm.*

// --------------- launch ---------------

/**
 * Launches a new *child coroutine* of [CoroutineScope] without blocking the current thread
 * and returns a reference to the coroutine as a [Job].
 *
 * [block] is the computation of the new coroutine that will run concurrently.
 * The coroutine is considered active until the block and all the child coroutines created in it finish.
 *
 * [context] specifies the additional context elements for the coroutine to combine with
 * the elements already present in the [CoroutineScope.coroutineContext].
 * It is incorrect to pass a [Job] element there, as this breaks structured concurrency.
 *
 * By default, the coroutine is scheduled for execution on its [ContinuationInterceptor].
 * There is no guarantee that it will start immediately: this is decided by the [ContinuationInterceptor].
 * It is possible that the new coroutine will be cancelled before starting, in which case its code will not be executed.
 * The [start] parameter can be used to adjust this behavior. See [CoroutineStart] for details.
 *
 * ## Structured Concurrency
 *
 * ### Coroutine context
 *
 * [launch] creates a *child coroutine* of `this` [CoroutineScope].
 *
 * The context of the new coroutine is created like this:
 * - First, the context of the [CoroutineScope] is combined with the [context] argument
 *   using the [newCoroutineContext] function.
 *   In most cases, this means that elements from [context] simply override
 *   the elements in the [CoroutineScope.coroutineContext].
 *   If no [ContinuationInterceptor] is present in the resulting context,
 *   then [Dispatchers.Default] is added there.
 * - Then, the [Job] in the [CoroutineScope.coroutineContext] is used as the *parent* of the new coroutine,
 *   unless overridden.
 *   Overriding the [Job] is forbidden; see a separate subsection below for details.
 *   The new coroutine's [Job] is added to the resulting context.
 *
 * The resulting coroutine context is the [coroutineContext] of the [CoroutineScope]
 * passed to the [block] as its receiver.
 *
 * The new coroutine is considered [active][isActive] until the [block] and all its child coroutines finish.
 * If the [block] throws a [CancellationException], the coroutine is considered cancelled,
 * and if it throws any other exception, the coroutine is considered failed.
 *
 * ### Interactions between coroutines
 *
 * The details of structured concurrency are described in the [CoroutineScope] interface documentation.
 * Here is a restatement of some main points as they relate to [launch]:
 *
 * - The lifecycle of the parent [CoroutineScope] can not end until this coroutine
 *   (as well as all its children) completes.
 * - If the parent [CoroutineScope] is cancelled, this coroutine is cancelled as well.
 * - If this coroutine fails with a non-[CancellationException] exception
 *   and the parent [CoroutineScope] has a non-supervisor [Job] in its context,
 *   the parent [Job] is cancelled with this exception.
 * - If this coroutine fails with an exception and the parent [CoroutineScope] has a supervisor [Job] or no job at all
 *   (as is the case with [GlobalScope] or malformed scopes),
 *   the exception is considered uncaught and is propagated as the [CoroutineExceptionHandler] documentation describes.
 * - The lifecycle of the [CoroutineScope] passed as the receiver to the [block]
 *   will not end until the [block] completes (or gets cancelled before ever having a chance to run).
 * - If the [block] throws a [CancellationException], the coroutine is considered cancelled,
 *   cancelling all its children in turn, but the parent does not get notified.
 *
 * ### Overriding the parent job
 *
 * Passing a [Job] in the [context] argument breaks structured concurrency and is not a supported pattern.
 * It does not throw an exception only for backward compatibility reasons, as a lot of code was written this way.
 * Always structure your coroutines such that the lifecycle of the child coroutine is
 * contained in the lifecycle of the [CoroutineScope] it is launched in.
 *
 * To help with migrating to structured concurrency, the specific behaviour of passing a [Job] in the [context] argument
 * is described here.
 * **Do not rely on this behaviour in new code.**
 *
 * If [context] contains a [Job] element, it will be the *parent* of the new coroutine,
 * and the lifecycle of the new coroutine will not be tied to the [CoroutineScope] at all.
 *
 * In specific terms:
 *
 * - If the [CoroutineScope] is cancelled, the new coroutine will not be affected.
 * - If the new coroutine fails with an exception, it will not cancel the [CoroutineScope].
 *   Instead, the exception will be propagated to the [Job] passed in the [context] argument.
 *   If that [Job] is a [SupervisorJob], the exception will be unhandled,
 *   and will be propagated as the [CoroutineExceptionHandler] documentation describes.
 *   If that [Job] is not a [SupervisorJob], it will be cancelled with the exception thrown by [launch].
 * - If the [CoroutineScope] is lexically scoped (for example, created by [coroutineScope] or [withContext]),
 *   the function defining the scope will not wait for the new coroutine to finish.
 *
 * ## Communicating with the coroutine
 *
 * [Job.cancel] can be used to cancel the coroutine, and [Job.join] can be used to block until its completion
 * without blocking the current thread.
 * Note that [Job.join] succeeds even if the coroutine was cancelled or failed with an exception.
 * [Job.cancelAndJoin] is a convenience function that combines cancellation and joining.
 *
 * If the coroutine was started with [start] set to [CoroutineStart.LAZY], the coroutine will not be scheduled
 * to run on its [ContinuationInterceptor] immediately.
 * [Job.start] can be used to start the coroutine explicitly,
 * and awaiting its completion using [Job.join] also causes the coroutine to start executing.
 *
 * A coroutine created with [launch] does not return a result, and if it fails with an exception,
 * there is no reliable way to learn about that exception in general.
 * [async] is a better choice if the result of the coroutine needs to be accessed from another coroutine.
 *
 * ## Differences from [async]
 *
 * [launch] is similar to [async] whose block returns a [Unit] value.
 *
 * The only difference is the handling of uncaught coroutine exceptions:
 * if an [async] coroutine fails with an exception, then even if the exception can not be propagated to the parent,
 * a [CoroutineExceptionHandler] will not be invoked.
 * Instead, the user of [async] must call [Deferred.await] to get the result of the coroutine,
 * which will be the uncaught exception.
 *
 * ## Pitfalls
 *
 * ### [CancellationException] silently stopping computations
 *
 * ```
 * val deferred = GlobalScope.async {
 *     awaitCancellation()
 * }
 * deferred.cancel()
 * coroutineScope {
 *     val job = launch {
 *         val result = deferred.await()
 *         println("Got $result")
 *     }
 *     job.join()
 *     println("Am I still not cancelled? $isActive")
 * }
 * ```
 *
 * will output
 *
 * ```
 * Am I still not cancelled? true
 * ```
 *
 * This may be surprising, because the `launch`ed coroutine failed with an exception,
 * but the parent still was not cancelled.
 *
 * The reason for this is that any [CancellationException] thrown in the coroutine is treated as a signal to cancel
 * the coroutine, but not the parent.
 * In this scenario, this is unlikely to be the desired behaviour:
 * this was a failure and not a cancellation and should be propagated to the parent.
 *
 * This is a legacy behavior that cannot be changed in a backward-compatible way.
 * Use [ensureActive] and [isActive] to distinguish between cancellation and failure:
 *
 * ```
 * launch {
 *     try {
 *         val result = deferred.await()
 *     } catch (e: CancellationException) {
 *         if (isActive) {
 *             // we were not cancelled, this is a failure
 *             println("`result` was cancelled")
 *             throw IllegalStateException("$result was cancelled", e)
 *         } else {
 *             println("I was cancelled")
 *             // throw again to finish the coroutine
 *             ensureActive()
 *         }
 *     }
 * }
 * ```
 *
 * In simpler scenarios, this form can be used:
 *
 * ```
 * launch {
 *     try {
 *         // operation that may throw its own CancellationException
 *     } catch (e: CancellationException) {
 *         ensureActive()
 *         throw IllegalStateException(e)
 *     }
 * }
 * ```
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param block the coroutine code which will be invoked in the child coroutine.
 **/
public fun CoroutineScope.launch(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> Unit
): Job {
    val newContext = newCoroutineContext(context)
    val coroutine = if (start.isLazy)
        LazyStandaloneCoroutine(newContext, block) else
        StandaloneCoroutine(newContext, active = true)
    coroutine.start(start, coroutine, block)
    return coroutine
}

// --------------- async ---------------

/**
 * Launches a new *child coroutine* of [CoroutineScope] without blocking the current thread
 * and returns a reference to the coroutine as a [Deferred] that can be used to access the final value.
 *
 * [block] is the computation of the new coroutine that will run concurrently.
 * The coroutine is considered active until the block and all the child coroutines created in it finish.
 * The result of executing the [block] is available via the returned [Deferred].
 *
 * [context] specifies the additional context elements for the coroutine to combine with
 * the elements already present in the [CoroutineScope.coroutineContext].
 * It is incorrect to pass a [Job] element there, as this breaks structured concurrency.
 *
 * By default, the coroutine is scheduled for execution on its [ContinuationInterceptor].
 * There is no guarantee that it will start immediately: this is decided by the [ContinuationInterceptor].
 * It is possible that the new coroutine will be cancelled before starting, in which case its code will not be executed.
 * The [start] parameter can be used to adjust this behavior. See [CoroutineStart] for details.
 *
 * ## Structured Concurrency
 *
 * ### Coroutine context
 *
 * [async] creates a *child coroutine* of `this` [CoroutineScope].
 *
 * See the corresponding subsection in the [launch] documentation for details on how the coroutine context is created.
 * In essence, the elements of [context] are combined with the elements of the [CoroutineScope.coroutineContext],
 * typically overriding them. It is incorrect to pass a [Job] element there, as this breaks structured concurrency.
 *
 * ### Interactions between coroutines
 *
 * The details of structured concurrency are described in the [CoroutineScope] interface documentation.
 * Here is a restatement of some main points as they relate to [async]:
 *
 * - The lifecycle of the parent [CoroutineScope] can not end until this coroutine
 *   (as well as all its children) completes.
 * - If the parent [CoroutineScope] is cancelled, this coroutine is cancelled as well.
 * - If this coroutine fails with a non-[CancellationException] exception
 *   and the parent [CoroutineScope] has a non-supervisor [Job] in its context,
 *   the parent [Job] is cancelled with this exception.
 * - If this coroutine fails with an exception and the parent [CoroutineScope] has a supervisor [Job] or no job at all
 *   (as is the case with [GlobalScope] or malformed scopes),
 *   the exception is considered uncaught and is only available through the returned [Deferred].
 * - The lifecycle of the [CoroutineScope] passed as the receiver to the [block]
 *   will not end until the [block] completes (or gets cancelled before ever having a chance to run).
 * - If the [block] throws a [CancellationException], the coroutine is considered cancelled,
 *   cancelling all its children in turn, but the parent does not get notified.
 *
 * ## Communicating with the coroutine
 *
 * [Deferred.await] can be used to suspend the current coroutine until the result of the [async] coroutine is available.
 * It returns the result of the [block] executed in the [async] coroutine.
 * Note that if the [async] coroutine fails with an exception, [Deferred.await] will also throw that exception,
 * including [CancellationException] if the coroutine was cancelled.
 * See the "CancellationException silently stopping computations" pitfall in the [launch] documentation.
 *
 * [Deferred.cancel] can be used to cancel the coroutine, and [Deferred.join] can be used to block until its completion
 * without blocking the current thread or accessing its result.
 * Note that [Deferred.join] succeeds even if the coroutine was cancelled or failed with an exception.
 * [Deferred.cancelAndJoin] is a convenience function that combines cancellation and joining.
 *
 * If the coroutine was started with [start] set to [CoroutineStart.LAZY], the coroutine will not be scheduled
 * to run on its [ContinuationInterceptor] immediately.
 * [Deferred.start] can be used to start the coroutine explicitly,
 * and awaiting its result using [Deferred.await] or [awaitAll] or its completion using [Deferred.join]
 * also causes the coroutine to start executing.
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param block the coroutine code which will be invoked in the child coroutine.
 */
public fun <T> CoroutineScope.async(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): Deferred<T> {
    val newContext = newCoroutineContext(context)
    val coroutine = if (start.isLazy)
        LazyDeferredCoroutine(newContext, block) else
        DeferredCoroutine<T>(newContext, active = true)
    coroutine.start(start, coroutine, block)
    return coroutine
}

@OptIn(InternalForInheritanceCoroutinesApi::class)
@Suppress("UNCHECKED_CAST")
private open class DeferredCoroutine<T>(
    parentContext: CoroutineContext,
    active: Boolean
) : AbstractCoroutine<T>(parentContext, true, active = active), Deferred<T> {
    override fun getCompleted(): T = getCompletedInternal() as T
    override suspend fun await(): T = awaitInternal() as T
    override val onAwait: SelectClause1<T> get() = onAwaitInternal as SelectClause1<T>
}

private class LazyDeferredCoroutine<T>(
    parentContext: CoroutineContext,
    block: suspend CoroutineScope.() -> T
) : DeferredCoroutine<T>(parentContext, active = false) {
    private val continuation = block.createCoroutineUnintercepted(this, this)

    override fun onStart() {
        continuation.startCoroutineCancellable(this)
    }
}

// --------------- withContext ---------------

/**
 * Calls the specified suspending [block] with an updated coroutine context, suspends until it completes, and returns
 * the result.
 *
 * [context] specifies the additional context elements for the coroutine to combine with
 * the elements already present in the [CoroutineScope.coroutineContext].
 * It is incorrect to pass a [Job] element there, as this breaks structured concurrency,
 * unless it is [NonCancellable].
 *
 * ## Structured Concurrency
 *
 * The behavior of [withContext] is similar to [coroutineScope], as it, too, creates a new *scoped child coroutine*.
 * Refer to the documentation of that function for details.
 *
 * The difference is that [withContext] does not simply call the [block] in a new coroutine
 * but updates the [currentCoroutineContext] used for running it.
 *
 * The context of the new scope is created like this:
 * - First, [currentCoroutineContext] is combined with the [context] argument.
 *   In most cases, this means that elements from [context] simply override
 *   the elements in the [currentCoroutineContext],
 *   but if they are `CopyableThreadContextElement`s, they are copied and combined as needed.
 * - Then, the [Job] in the [currentCoroutineContext], if any, is used as the *parent* of the new scope,
 *   unless overridden.
 *   Overriding the [Job] is forbidden with the notable exception of [NonCancellable];
 *   see a separate subsection below for details.
 *   The new scope's [Job] is added to the resulting context.
 *
 * The context of the new scope is obtained by combining the [currentCoroutineContext] with a new [Job]
 * whose parent is the [Job] of the caller [currentCoroutineContext] (if any).
 * The [Job] of the new scope is not a normal child of the caller coroutine but a lexically scoped one,
 * meaning that the failure of the [Job] will not affect the parent [Job].
 * Instead, the exception leading to the failure will be rethrown to the caller of this function.
 *
 * ### Overriding the parent job
 *
 * #### [NonCancellable]
 *
 * Passing [NonCancellable] in the [context] argument is a special case that allows
 * the [block] to run even if the parent coroutine is cancelled.
 *
 * This is useful in particular for performing cleanup operations
 * if the cleanup procedure is itself a `suspend` function.
 *
 * Example:
 *
 * ```
 * class Connection {
 *     suspend fun terminate()
 * }
 *
 * val connection = Connection()
 * try {
 *     // some cancellable operations...
 * } finally {
 *     withContext(NonCancellable) {
 *         // this block will run even if the parent coroutine is cancelled
 *         connection.terminate()
 *     }
 * }
 * ```
 *
 * Beware that combining [NonCancellable] with context elements that change the dispatcher
 * will make this cleanup code incorrect. See the [NonCancellable] documentation for details.
 *
 * #### Other [Job] elements
 *
 * Passing a [Job] in the [context] argument breaks structured concurrency and is not a supported pattern.
 * It does not throw an exception only for backward compatibility reasons, as a lot of code was written this way.
 * Always structure your coroutines such that the lifecycle of the child coroutine is
 * contained in the lifecycle of the [CoroutineScope] it is launched in.
 *
 * To help with migrating to structured concurrency, the specific behaviour of passing a [Job] in the [context] argument
 * is described here.
 * **Do not rely on this behaviour in new code.**
 *
 * If [context] contains a [Job] element, it will be the *parent* of the new coroutine,
 * and the lifecycle of the new coroutine will not be tied to the [CoroutineScope] at all.
 *
 * In specific terms:  
 *
 * - If the [currentCoroutineContext] is cancelled, the new coroutine will not be affected.
 * - In particular, if [withContext] avoided a dispatch (see "Dispatching behavior" below)
 *   and its block finished without an exception, [withContext] itself will not throw a [CancellationException].
 *
 * ## Dispatching behavior
 *
 * [withContext] attempts to avoid additional dispatches if the [context] argument does not change the
 *
 * The resulting context for the [block] is derived by merging the current [coroutineContext] with the
 * specified [context] using `coroutineContext + context` (see [CoroutineContext.plus]).
 * This suspending function is cancellable. It immediately checks for cancellation of
 * the resulting context and throws [CancellationException] if it is not [active][CoroutineContext.isActive].
 *
 * Calls to [withContext] whose [context] argument provides a [CoroutineDispatcher] that is
 * different from the current one, by necessity, perform additional dispatches: the [block]
 * can not be executed immediately and needs to be dispatched for execution on
 * the passed [CoroutineDispatcher], and then when the [block] completes, the execution
 * has to shift back to the original dispatcher.
 *
 * Note that the result of `withContext` invocation is dispatched into the original context in a cancellable way
 * with a **prompt cancellation guarantee**, which means that if the original [coroutineContext]
 * in which `withContext` was invoked is cancelled by the time its dispatcher starts to execute the code,
 * it discards the result of `withContext` and throws [CancellationException].
 *
 * The cancellation behaviour described above is enabled if and only if the dispatcher is being changed.
 * For example, when using `withContext(NonCancellable) { ... }` there is no change in dispatcher and
 * this call will not be cancelled neither on entry to the block inside `withContext` nor on exit from it.
 */
public suspend fun <T> withContext(
    context: CoroutineContext,
    block: suspend CoroutineScope.() -> T
): T {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    return suspendCoroutineUninterceptedOrReturn sc@ { uCont ->
        // compute new context
        val oldContext = uCont.context
        // Copy CopyableThreadContextElement if necessary
        val newContext = oldContext.newCoroutineContext(context)
        // always check for cancellation of new context
        newContext.ensureActive()
        // FAST PATH #1 -- new context is the same as the old one
        if (newContext === oldContext) {
            val coroutine = ScopeCoroutine(newContext, uCont)
            return@sc coroutine.startUndispatchedOrReturn(coroutine, block)
        }
        // FAST PATH #2 -- the new dispatcher is the same as the old one (something else changed)
        // `equals` is used by design (see equals implementation is wrapper context like ExecutorCoroutineDispatcher)
        if (newContext[ContinuationInterceptor] == oldContext[ContinuationInterceptor]) {
            val coroutine = UndispatchedCoroutine(newContext, uCont)
            // There are changes in the context, so this thread needs to be updated
            withCoroutineContext(coroutine.context, null) {
                return@sc coroutine.startUndispatchedOrReturn(coroutine, block)
            }
        }
        // SLOW PATH -- use new dispatcher
        val coroutine = DispatchedCoroutine(newContext, uCont)
        block.startCoroutineCancellable(coroutine, coroutine)
        coroutine.getResult()
    }
}

/**
 * Calls the specified suspending block with the given [CoroutineDispatcher], suspends until it
 * completes, and returns the result.
 *
 * This inline function calls [withContext].
 */
public suspend inline operator fun <T> CoroutineDispatcher.invoke(
    noinline block: suspend CoroutineScope.() -> T
): T = withContext(this, block)

// --------------- implementation ---------------

private open class StandaloneCoroutine(
    parentContext: CoroutineContext,
    active: Boolean
) : AbstractCoroutine<Unit>(parentContext, initParentJob = true, active = active) {
    override fun handleJobException(exception: Throwable): Boolean {
        handleCoroutineException(context, exception)
        return true
    }
}

private class LazyStandaloneCoroutine(
    parentContext: CoroutineContext,
    block: suspend CoroutineScope.() -> Unit
) : StandaloneCoroutine(parentContext, active = false) {
    private val continuation = block.createCoroutineUnintercepted(this, this)

    override fun onStart() {
        continuation.startCoroutineCancellable(this)
    }
}

// Used by withContext when context changes, but dispatcher stays the same
internal expect class UndispatchedCoroutine<in T>(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>

private const val UNDECIDED = 0
private const val SUSPENDED = 1
private const val RESUMED = 2

// Used by withContext when context dispatcher changes
internal class DispatchedCoroutine<in T>(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context, uCont) {
    // this is copy-and-paste of a decision state machine inside AbstractionContinuation
    // todo: we may some-how abstract it via inline class
    private val _decision = atomic(UNDECIDED)

    private fun trySuspend(): Boolean {
        _decision.loop { decision ->
            when (decision) {
                UNDECIDED -> if (this._decision.compareAndSet(UNDECIDED, SUSPENDED)) return true
                RESUMED -> return false
                else -> error("Already suspended")
            }
        }
    }

    private fun tryResume(): Boolean {
        _decision.loop { decision ->
            when (decision) {
                UNDECIDED -> if (this._decision.compareAndSet(UNDECIDED, RESUMED)) return true
                SUSPENDED -> return false
                else -> error("Already resumed")
            }
        }
    }

    override fun afterCompletion(state: Any?) {
        // Call afterResume from afterCompletion and not vice-versa, because stack-size is more
        // important for afterResume implementation
        afterResume(state)
    }

    override fun afterResume(state: Any?) {
        if (tryResume()) return // completed before getResult invocation -- bail out
        // Resume in a cancellable way because we have to switch back to the original dispatcher
        uCont.intercepted().resumeCancellableWith(recoverResult(state, uCont))
    }

    internal fun getResult(): Any? {
        if (trySuspend()) return COROUTINE_SUSPENDED
        // otherwise, onCompletionInternal was already invoked & invoked tryResume, and the result is in the state
        val state = this.state.unboxState()
        if (state is CompletedExceptionally) throw state.cause
        @Suppress("UNCHECKED_CAST")
        return state as T
    }
}
