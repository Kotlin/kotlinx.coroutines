/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("BuildersKt")

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.jvm.*

// --------------- launch ---------------

/**
 * Launches new coroutine without blocking current thread and returns a reference to the coroutine as a [Job].
 * The coroutine is cancelled when the resulting job is [cancelled][Job.cancel].
 *
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * by a job specified in the [context].
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other start options can be specified via `start` parameter. See [CoroutineStart] for details.
 * An optional [start] parameter can be set to [CoroutineStart.LAZY] to start coroutine _lazily_. In this case,
 * the coroutine [Job] is created in _new_ state. It can be explicitly started with [start][Job.start] function
 * and will be started implicitly on the first invocation of [join][Job.join].
 *
 * ### Exception handling
 *
 * _Uncaught exception_ in this coroutine cancels parent job in the context,
 * which means that when `launch` is used within the context of another coroutine,
 * then any uncaught exception leads to the cancellation of the parent coroutine.
 * If a coroutine has no parent (if it was started from [GlobalScope] or a [Job] is its context
 * was explicitly overridden by either [NonCancellable] or `Job()`), then uncaught exceptions
 * a handled by [CoroutineExceptionHandler] in its context.
 *
 * In order to catch exception that occurs inside the launched coroutine and all its children, the body
 * of the coroutine has to be wrapped in the following way:
 *
 * ```
 * val job = launch {
 *    try {
 *        coroutineScope { // to catch all children exceptions
 *            // ... body of the coroutine ...
 *        }
 *    } catch (e: ExceptionToCatch) {
 *        handleException(e)
 *    } finally {
 *       cleanup()
 *    }
 * }
 * ```
 *
 * However, if this `job` is [cancelled][Job.cancel], then `cleanup()` is executed in the context of the
 * already cancelled [Job]. The same happens for `handleException` if [CancellationException] is being caught.
 * Any cancellable suspending function would itself throw a [CancellationException]. So, any suspending
 * code has to be wrapped into `withContext(NonCancellable) { ... }` (see [NonCancellable]).
 *
 * A simpler way to handle exceptions is provided via [launchBuilder] function. It takes the same parameters
 * as `launch`, but allows to specify [`catch`][CoroutineBuilder.catch] and [`finally`][CoroutineBuilder.finally]
 * clauses before building a coroutine with [`build`][CoroutineBuilder.build].
 * In this way, the proper non-cancellable context is already established for `catch` and `finally` blocks:
 *
 * ```
 * val job = launchBuilder {
 *     // ... body of the coroutine ...
 * }.catch<ExceptionToCatch> { e ->
 *     handleException(e)
 * }.finally {
 *     cleanup()
 * }.build()
 * ```
 *
 * See [CoroutineBuilder] for details.
 *
 * ### Debugging
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param block the coroutine code which will be invoked in the context of the provided scope.
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

/**
 * Creates a builder for [launch] call, so that exception handlers can be conveniently defined
 * using [`catch`][CoroutineBuilder.catch] and [`finally`][CoroutineBuilder.finally]. The coroutine is
 * created at the end of builder chain with [`build`][CoroutineBuilder.build].
 *
 * For example:
 *
 * ```
 * val job = launchBuilder {
 *     // ... body of the coroutine ...
 * }.catch<ExceptionToCatch> { e ->
 *     handleException(e)
 * }.finally {
 *     cleanup()
 * }.build()
 * ```
 * 
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param block the coroutine code which will be invoked in the context of the provided scope.
 */
@ExperimentalCoroutinesApi // Introduced in 1.2.0, tentatively to be stabilized in 1.3.0
public fun CoroutineScope.launchBuilder(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> Unit
): CoroutineBuilder<Job, CoroutineScope, Unit> =
    LaunchBuilder(this, context, start, CoroutineBuilder.Clauses(block))

private class LaunchBuilder(
    private val scope: CoroutineScope,
    private val context: CoroutineContext = EmptyCoroutineContext,
    private val start: CoroutineStart = CoroutineStart.DEFAULT,
    clauses: CoroutineBuilder.Clauses<CoroutineScope, Unit>
) : CoroutineBuilder<Job, CoroutineScope, Unit>(clauses) {
    @InternalCoroutinesApi
    override fun updateClauses(clauses: Clauses<CoroutineScope, Unit>): CoroutineBuilder<Job, CoroutineScope, Unit> =
        LaunchBuilder(scope, context, start, clauses)
    override fun build(): Job = scope.launch(context, start, current.block)
}

// --------------- async ---------------

/**
 * Creates new coroutine and returns its future result as an implementation of [Deferred].
 * The running coroutine is cancelled when the resulting deferred is [cancelled][Job.cancel].
 *
 * Coroutine context is inherited from a [CoroutineScope], additional context elements can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from a [CoroutineScope] as well, but it can also be overridden
 * with corresponding [coroutineContext] element.
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 * An optional [start] parameter can be set to [CoroutineStart.LAZY] to start coroutine _lazily_. In this case,
 * the resulting [Deferred] is created in _new_ state. It can be explicitly started with [start][Job.start]
 * function and will be started implicitly on the first invocation of [join][Job.join], [await][Deferred.await] or [awaitAll].
 *
 * ### Exception handling
 *
 * _Uncaught exception_ in this coroutine cancels parent job in the context,
 * which means that when `async` is used within the context of another coroutine,
 * then any uncaught exception leads to the cancellation of the parent coroutine.
 * If a coroutine has no parent (if it was started from [GlobalScope] or a [Job] is its context
 * was explicitly overridden by either [NonCancellable] or `Job()`), then uncaught exceptions
 * a **not** handled by [CoroutineExceptionHandler] in its context &mdash; they are supposed to be
 * handled by the code that works with the resulting [Deferred].
 *
 * In order to catch exception that occurs inside the async coroutine and all its children, the body
 * of the coroutine has to be wrapped in the following way:
 *
 * ```
 * val deferred = async {
 *    try {
 *        coroutineScope { // to catch all children exceptions
 *            // ... body of the coroutine ...
 *        }
 *    } catch (e: ExceptionToCatch) {
 *        handleException(e)
 *    } finally {
 *       cleanup()
 *    }
 * }
 * ```
 *
 * However, if this `deferred` is [cancelled][Job.cancel], then `cleanup()` is executed in the context of the
 * already cancelled [Job]. The same happens for `handleException` if [CancellationException] is being caught.
 * Any cancellable suspending function would itself throw a [CancellationException]. So, any suspending
 * code has to be wrapped into `withContext(NonCancellable) { ... }` (see [NonCancellable]).
 *
 * A simpler way to handle exceptions is provided via [asyncBuilder] function. It takes the same parameters
 * as `async`, but allows to specify [`catch`][CoroutineBuilder.catch] and [`finally`][CoroutineBuilder.finally]
 * clauses before building a coroutine with [`build`][CoroutineBuilder.build].
 * In this way, the proper non-cancellable context is already established for `catch` and `finally` blocks:
 *
 * ```
 * val deferred = asyncBuilder {
 *     // ... body of the coroutine ...
 * }.catch<ExceptionToCatch> { e ->
 *     handleException(e)
 * }.finally {
 *     cleanup()
 * }.build()
 * ```
 *
 * See [CoroutineBuilder] for details.
 *
 * ### Debugging
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param block the coroutine code.
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

/**
 * Creates a builder for [async] call, so that exception handlers can be conveniently defined
 * using [`catch`][CoroutineBuilder.catch] and [`finally`][CoroutineBuilder.finally]. The coroutine is
 * created at the end of builder chain with [`build`][CoroutineBuilder.build].
 *
 * For example:
 *
 * ```
 * val deferred = asyncBuilder {
 *     // ... body of the coroutine ...
 * }.catch<ExceptionToCatch> { e ->
 *     handleException(e)
 * }.finally {
 *     cleanup()
 * }.build()
 * ```
 *
 * @param context additional to [CoroutineScope.coroutineContext] context of the coroutine.
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param block the coroutine code.
 */
@ExperimentalCoroutinesApi // Introduced in 1.2.0, tentatively to be stabilized in 1.3.0
public fun <T> CoroutineScope.asyncBuilder(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): CoroutineBuilder<Deferred<T>, CoroutineScope, T> =
    AsyncBuilder(this, context, start, CoroutineBuilder.Clauses(block))

private class AsyncBuilder<T>(
    private val scope: CoroutineScope,
    private val context: CoroutineContext = EmptyCoroutineContext,
    private val start: CoroutineStart = CoroutineStart.DEFAULT,
    clauses: CoroutineBuilder.Clauses<CoroutineScope, T>
): CoroutineBuilder<Deferred<T>, CoroutineScope, T>(clauses) {
    override fun updateClauses(clauses: Clauses<CoroutineScope, T>): CoroutineBuilder<Deferred<T>, CoroutineScope, T> =
        AsyncBuilder(scope, context, start, clauses)

    @Suppress("DeferredIsResult")
    override fun build(): Deferred<T> =
        scope.async(context, start, current.block)
}

@Suppress("UNCHECKED_CAST")
private open class DeferredCoroutine<T>(
    parentContext: CoroutineContext,
    active: Boolean
) : AbstractCoroutine<T>(parentContext, active), Deferred<T>, SelectClause1<T> {
    override fun getCompleted(): T = getCompletedInternal() as T
    override suspend fun await(): T = awaitInternal() as T
    override val onAwait: SelectClause1<T> get() = this
    override fun <R> registerSelectClause1(select: SelectInstance<R>, block: suspend (T) -> R) =
        registerSelectClause1Internal(select, block)
}

private class LazyDeferredCoroutine<T>(
    parentContext: CoroutineContext,
    block: suspend CoroutineScope.() -> T
) : DeferredCoroutine<T>(parentContext, active = false) {
    private var block: (suspend CoroutineScope.() -> T)? = block

    override fun onStart() {
        val block = checkNotNull(this.block) { "Already started" }
        this.block = null
        block.startCoroutineCancellable(this, this)
    }
}

// --------------- withContext ---------------

/**
 * Calls the specified suspending block with a given coroutine context, suspends until it completes, and returns
 * the result.
 *
 * The resulting context for the [block] is derived by merging the current [coroutineContext] with the
 * specified [context] using `coroutineContext + context` (see [CoroutineContext.plus]).
 * This suspending function is cancellable. It immediately checks for cancellation of
 * the resulting context and throws [CancellationException] if it is not [active][CoroutineContext.isActive].
 *
 * This function uses dispatcher from the new context, shifting execution of the [block] into the
 * different thread if a new dispatcher is specified, and back to the original dispatcher
 * when it completes. Note, that the result of `withContext` invocation is
 * dispatched into the original context in a cancellable way, which means that if the original [coroutineContext],
 * in which `withContext` was invoked, is cancelled by the time its dispatcher starts to execute the code,
 * it discards the result of `withContext` and throws [CancellationException].
 */
public suspend fun <T> withContext(
    context: CoroutineContext,
    block: suspend CoroutineScope.() -> T
): T = suspendCoroutineUninterceptedOrReturn sc@ { uCont ->
    // compute new context
    val oldContext = uCont.context
    val newContext = oldContext + context
    // always check for cancellation of new context
    newContext.checkCompletion()
    // FAST PATH #1 -- new context is the same as the old one
    if (newContext === oldContext) {
        val coroutine = ScopeCoroutine(newContext, uCont) // MODE_DIRECT
        return@sc coroutine.startUndispatchedOrReturn(coroutine, block)
    }
    // FAST PATH #2 -- the new dispatcher is the same as the old one (something else changed)
    // `equals` is used by design (see equals implementation is wrapper context like ExecutorCoroutineDispatcher)
    if (newContext[ContinuationInterceptor] == oldContext[ContinuationInterceptor]) {
        val coroutine = UndispatchedCoroutine(newContext, uCont) // MODE_UNDISPATCHED
        // There are changes in the context, so this thread needs to be updated
        withCoroutineContext(newContext, null) {
            return@sc coroutine.startUndispatchedOrReturn(coroutine, block)
        }
    }
    // SLOW PATH -- use new dispatcher
    val coroutine = DispatchedCoroutine(newContext, uCont) // MODE_ATOMIC_DEFAULT
    coroutine.initParentJob()
    block.startCoroutineCancellable(coroutine, coroutine)
    coroutine.getResult()
}

/**
 * Optimized internal version of [withContext] that is essentially equivalent to
 * `withContext(NonCancellable) { block(param) }`.
 */
internal suspend fun <P, T> withNonCancellableContext(
    param: P,
    block: suspend CoroutineScope.(P) -> T
): T = suspendCoroutineUninterceptedOrReturn sc@ { uCont ->
    // compute new context
    val oldContext = uCont.context
    val newContext = oldContext.minusKey(Job) // is not going to be a child of the parent job
    val coroutine = UndispatchedCoroutine(newContext, uCont) // MODE_UNDISPATCHED
    // todo: lambda allocation in the below code can be optimized away
    return@sc coroutine.startUndispatchedOrReturn(coroutine) {
        block(param)
    }
}

/**
 * Calls the specified suspending block with the given [CoroutineDispatcher], suspends until it
 * completes, and returns the result.
 *
 * This inline function calls [withContext].
 */
@ExperimentalCoroutinesApi
public suspend inline operator fun <T> CoroutineDispatcher.invoke(
    noinline block: suspend CoroutineScope.() -> T
): T = withContext(this, block)

// --------------- implementation ---------------

private open class StandaloneCoroutine(
    parentContext: CoroutineContext,
    active: Boolean
) : AbstractCoroutine<Unit>(parentContext, active) {
    override fun handleJobException(exception: Throwable): Boolean {
        handleCoroutineException(context, exception)
        return true
    }
}

private class LazyStandaloneCoroutine(
    parentContext: CoroutineContext,
    block: suspend CoroutineScope.() -> Unit
) : StandaloneCoroutine(parentContext, active = false) {
    private var block: (suspend CoroutineScope.() -> Unit)? = block

    override fun onStart() {
        val block = checkNotNull(this.block) { "Already started" }
        this.block = null
        block.startCoroutineCancellable(this, this)
    }
}

// Used by withContext when context changes, but dispatcher stays the same
private class UndispatchedCoroutine<in T>(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context, uCont) {
    override val defaultResumeMode: Int get() = MODE_UNDISPATCHED
}

private const val UNDECIDED = 0
private const val SUSPENDED = 1
private const val RESUMED = 2

// Used by withContext when context dispatcher changes
private class DispatchedCoroutine<in T>(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context, uCont) {
    override val defaultResumeMode: Int get() = MODE_ATOMIC_DEFAULT

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

    override fun onCompletionInternal(state: Any?, mode: Int) {
        if (tryResume()) return // completed before getResult invocation -- bail out
        // otherwise, getResult has already commenced, i.e. completed later or in other thread
        super.onCompletionInternal(state, mode)
    }

    fun getResult(): Any? {
        if (trySuspend()) return COROUTINE_SUSPENDED
        // otherwise, onCompletionInternal was already invoked & invoked tryResume, and the result is in the state
        val state = this.state.unboxState()
        if (state is CompletedExceptionally) throw state.cause
        @Suppress("UNCHECKED_CAST")
        return state as T
    }
}
