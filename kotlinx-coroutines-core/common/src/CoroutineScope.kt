/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:OptIn(ExperimentalContracts::class)

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/**
 * Defines a scope for new coroutines. Every **coroutine builder** (like [launch], [async], etc)
 * is an extension on [CoroutineScope] and inherits its [coroutineContext][CoroutineScope.coroutineContext]
 * to automatically propagate all its elements and cancellation.
 *
 * The best ways to obtain a standalone instance of the scope are [CoroutineScope()] and [MainScope()] factory functions,
 * taking care to cancel these coroutine scopes when they are no longer needed (see section on custom usage below for
 * explanation and example).
 *
 * Additional context elements can be appended to the scope using the [plus][CoroutineScope.plus] operator.
 *
 * ### Convention for structured concurrency
 *
 * Manual implementation of this interface is not recommended, implementation by delegation should be preferred instead.
 * By convention, the [context of a scope][CoroutineScope.coroutineContext] should contain an instance of a
 * [job][Job] to enforce the discipline of **structured concurrency** with propagation of cancellation.
 *
 * Every coroutine builder (like [launch], [async], etc)
 * and every scoping function (like [coroutineScope], [withContext], etc) provides _its own_ scope
 * with its own [Job] instance into the inner block of code it runs.
 * By convention, they all wait for all the coroutines inside their block to complete before completing themselves,
 * thus enforcing the structured concurrency. See [Job] documentation for more details.
 *
 * ### Android usage
 *
 * Android has first-party support for coroutine scope in all entities with the lifecycle.
 * See [the corresponding documentation](https://developer.android.com/topic/libraries/architecture/coroutines#lifecyclescope).
 *
 * ### Custom usage
 *
 * `CoroutineScope` should be declared as a property on entities with a well-defined lifecycle that are
 * responsible for launching children coroutines. The corresponding instance of `CoroutineScope` shall be created
 * with either `CoroutineScope()` or `MainScope()` functions. The difference between them is only in the
 * [CoroutineDispatcher]:
 *
 * * `CoroutineScope()` uses [Dispatchers.Default] for its coroutines.
 * * `MainScope()` uses [Dispatchers.Main] for its coroutines.
 *
 * **The key part of custom usage of `CustomScope` is cancelling it at the end of the lifecycle.**
 * The [CoroutineScope.cancel] extension function shall be used when the entity that was launching coroutines
 * is no longer needed. It cancels all the coroutines that might still be running on behalf of it.
 *
 * For example:
 *
 * ```
 * class MyUIClass {
 *     val scope = MainScope() // the scope of MyUIClass, uses Dispatchers.Main
 *
 *     fun destroy() { // destroys an instance of MyUIClass
 *         scope.cancel() // cancels all coroutines launched in this scope
 *         // ... do the rest of cleanup here ...
 *     }
 *
 *     /*
 *      * Note: if this instance is destroyed or any of the launched coroutines
 *      * in this method throws an exception, then all nested coroutines are cancelled.
 *      */
 *     fun showSomeData() = scope.launch { // launched in the main thread
 *        // ... here we can use suspending functions or coroutine builders with other dispatchers
 *        draw(data) // draw in the main thread
 *     }
 * }
 * ```
 */
public interface CoroutineScope {
    /**
     * The context of this scope.
     * Context is encapsulated by the scope and used for implementation of coroutine builders that are extensions on the scope.
     * Accessing this property in general code is not recommended for any purposes except accessing the [Job] instance for advanced usages.
     *
     * By convention, should contain an instance of a [job][Job] to enforce structured concurrency.
     */
    public val coroutineContext: CoroutineContext
}

/**
 * Adds the specified coroutine context to this scope, overriding existing elements in the current
 * scope's context with the corresponding keys.
 *
 * This is a shorthand for `CoroutineScope(thisScope + context)`.
 */
public operator fun CoroutineScope.plus(context: CoroutineContext): CoroutineScope =
    ContextScope(coroutineContext + context)

/**
 * Creates the main [CoroutineScope] for UI components.
 *
 * Example of use:
 * ```
 * class MyAndroidActivity {
 *     private val scope = MainScope()
 *
 *     override fun onDestroy() {
 *         super.onDestroy()
 *         scope.cancel()
 *     }
 * }
 * ```
 *
 * The resulting scope has [SupervisorJob] and [Dispatchers.Main] context elements.
 * If you want to append additional elements to the main scope, use [CoroutineScope.plus] operator:
 * `val scope = MainScope() + CoroutineName("MyActivity")`.
 */
@Suppress("FunctionName")
public fun MainScope(): CoroutineScope = ContextScope(SupervisorJob() + Dispatchers.Main)

/**
 * Returns `true` when the current [Job] is still active (has not completed and was not cancelled yet).
 *
 * Check this property in long-running computation loops to support cancellation:
 * ```
 * while (isActive) {
 *     // do some computation
 * }
 * ```
 *
 * This property is a shortcut for `coroutineContext.isActive` in the scope when
 * [CoroutineScope] is available.
 * See [coroutineContext][kotlin.coroutines.coroutineContext],
 * [isActive][kotlinx.coroutines.isActive] and [Job.isActive].
 */
@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
public val CoroutineScope.isActive: Boolean
    get() = coroutineContext[Job]?.isActive ?: true

/**
 * A global [CoroutineScope] not bound to any job.
 * Global scope is used to launch top-level coroutines which are operating on the whole application lifetime
 * and are not cancelled prematurely.
 *
 * Active coroutines launched in `GlobalScope` do not keep the process alive. They are like daemon threads.
 *
 * This is a **delicate** API. It is easy to accidentally create resource or memory leaks when
 * `GlobalScope` is used. A coroutine launched in `GlobalScope` is not subject to the principle of structured
 * concurrency, so if it hangs or gets delayed due to a problem (e.g. due to a slow network), it will stay working
 * and consuming resources. For example, consider the following code:
 *
 * ```
 * fun loadConfiguration() {
 *     GlobalScope.launch {
 *         val config = fetchConfigFromServer() // network request
 *         updateConfiguration(config)
 *     }
 * }
 * ```
 *
 * A call to `loadConfiguration` creates a coroutine in the `GlobalScope` that works in background without any
 * provision to cancel it or to wait for its completion. If a network is slow, it keeps waiting in background,
 * consuming resources. Repeated calls to `loadConfiguration` will consume more and more resources.
 *
 * ### Possible replacements
 *
 * In many cases uses of `GlobalScope` should be removed, marking the containing operation with `suspend`, for example:
 *
 * ```
 * suspend fun loadConfiguration() {
 *     val config = fetchConfigFromServer() // network request
 *     updateConfiguration(config)
 * }
 * ```
 *
 * In cases when `GlobalScope.launch` was used to launch multiple concurrent operations, the corresponding
 * operations shall be grouped with [coroutineScope] instead:
 *
 * ```
 * // concurrently load configuration and data
 * suspend fun loadConfigurationAndData() {
 *     coroutinesScope {
 *         launch { loadConfiguration() }
 *         launch { loadData() }
 *     }
 * }
 * ```
 *
 * In top-level code, when launching a concurrent operation from a non-suspending context, an appropriately
 * confined instance of [CoroutineScope] shall be used instead of a `GlobalScope`. See docs on [CoroutineScope] for
 * details.
 *
 * ### GlobalScope vs custom scope
 *
 * Do not replace `GlobalScope.launch { ... }` with `CoroutineScope().launch { ... }` constructor function call.
 * The latter has the same pitfalls as `GlobalScope`. See [CoroutineScope] documentation on the intended usage of
 * `CoroutineScope()` constructor function.
 *
 * ### Legitimate use-cases
 *
 * There are limited circumstances under which `GlobalScope` can be legitimately and safely used, such as top-level background
 * processes that must stay active for the whole duration of the application's lifetime. Because of that, any use
 * of `GlobalScope` requires an explicit opt-in with `@OptIn(DelicateCoroutinesApi::class)`, like this:
 *
 * ```
 * // A global coroutine to log statistics every second, must be always active
 * @OptIn(DelicateCoroutinesApi::class)
 * val globalScopeReporter = GlobalScope.launch {
 *     while (true) {
 *         delay(1000)
 *         logStatistics()
 *     }
 * }
 * ```
 */
@DelicateCoroutinesApi
public object GlobalScope : CoroutineScope {
    /**
     * Returns [EmptyCoroutineContext].
     */
    override val coroutineContext: CoroutineContext
        get() = EmptyCoroutineContext
}

/**
 * Creates a [CoroutineScope] and calls the specified suspend block with this scope.
 * The provided scope inherits its [coroutineContext][CoroutineScope.coroutineContext] from the outer scope, but overrides
 * the context's [Job].
 *
 * This function is designed for _parallel decomposition_ of work. When any child coroutine in this scope fails,
 * this scope fails and all the rest of the children are cancelled (for a different behavior see [supervisorScope]).
 * This function returns as soon as the given block and all its children coroutines are completed.
 * A usage example of a scope looks like this:
 *
 * ```
 * suspend fun showSomeData() = coroutineScope {
 *     val data = async(Dispatchers.IO) { // <- extension on current scope
 *      ... load some UI data for the Main thread ...
 *     }
 *
 *     withContext(Dispatchers.Main) {
 *         doSomeWork()
 *         val result = data.await()
 *         display(result)
 *     }
 * }
 * ```
 *
 * The scope in this example has the following semantics:
 * 1) `showSomeData` returns as soon as the data is loaded and displayed in the UI.
 * 2) If `doSomeWork` throws an exception, then the `async` task is cancelled and `showSomeData` rethrows that exception.
 * 3) If the outer scope of `showSomeData` is cancelled, both started `async` and `withContext` blocks are cancelled.
 * 4) If the `async` block fails, `withContext` will be cancelled.
 *
 * The method may throw a [CancellationException] if the current job was cancelled externally
 * or may throw a corresponding unhandled [Throwable] if there is any unhandled exception in this scope
 * (for example, from a crashed coroutine that was started with [launch][CoroutineScope.launch] in this scope).
 */
public suspend fun <R> coroutineScope(block: suspend CoroutineScope.() -> R): R {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    return suspendCoroutineUninterceptedOrReturn { uCont ->
        val coroutine = ScopeCoroutine(uCont.context, uCont)
        coroutine.startUndispatchedOrReturn(coroutine, block)
    }
}

/**
 * Creates a [CoroutineScope] that wraps the given coroutine [context].
 *
 * If the given [context] does not contain a [Job] element, then a default `Job()` is created.
 * This way, cancellation or failure of any child coroutine in this scope cancels all the other children,
 * just like inside [coroutineScope] block.
 */
@Suppress("FunctionName")
public fun CoroutineScope(context: CoroutineContext): CoroutineScope =
    ContextScope(if (context[Job] != null) context else context + Job())

/**
 * Cancels this scope, including its job and all its children with an optional cancellation [cause].
 * A cause can be used to specify an error message or to provide other details on
 * a cancellation reason for debugging purposes.
 * Throws [IllegalStateException] if the scope does not have a job in it.
 */
public fun CoroutineScope.cancel(cause: CancellationException? = null) {
    val job = coroutineContext[Job] ?: error("Scope cannot be cancelled because it does not have a job: $this")
    job.cancel(cause)
}

/**
 * Cancels this scope, including its job and all its children with a specified diagnostic error [message].
 * A [cause] can be specified to provide additional details on a cancellation reason for debugging purposes.
 * Throws [IllegalStateException] if the scope does not have a job in it.
 */
public fun CoroutineScope.cancel(message: String, cause: Throwable? = null): Unit = cancel(CancellationException(message, cause))

/**
 * Ensures that current scope is [active][CoroutineScope.isActive].
 *
 * If the job is no longer active, throws [CancellationException].
 * If the job was cancelled, thrown exception contains the original cancellation cause.
 * This function does not do anything if there is no [Job] in the scope's [coroutineContext][CoroutineScope.coroutineContext].
 *
 * This method is a drop-in replacement for the following code, but with more precise exception:
 * ```
 * if (!isActive) {
 *     throw CancellationException()
 * }
 * ```
 *
 * @see CoroutineContext.ensureActive
 */
public fun CoroutineScope.ensureActive(): Unit = coroutineContext.ensureActive()


/**
 * Returns the current [CoroutineContext] retrieved by using [kotlin.coroutines.coroutineContext].
 * This function is an alias to avoid name clash with [CoroutineScope.coroutineContext] in a receiver position:
 *
 * ```
 * launch { // this: CoroutineScope
 *     val flow = flow<Unit> {
 *         coroutineContext // Resolves into the context of outer launch, which is incorrect, see KT-38033
 *         currentCoroutineContext() // Retrieves actual context where the flow is collected
 *     }
 * }
 * ```
 */
public suspend inline fun currentCoroutineContext(): CoroutineContext = coroutineContext
