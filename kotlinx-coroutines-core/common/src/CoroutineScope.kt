@file:OptIn(ExperimentalContracts::class)

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/**
 * Defines a scope for new coroutines. Every **coroutine builder** (like [launch], [async], etc.)
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
 * Every coroutine builder (like [launch], [async], and others)
 * and every scoping function (like [coroutineScope] and [withContext]) provides _its own_ scope
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
 * responsible for launching child coroutines. The corresponding instance of `CoroutineScope` shall be created
 * with either `CoroutineScope()` or `MainScope()`:
 *
 * - `CoroutineScope()` uses the [context][CoroutineContext] provided to it as a parameter for its coroutines 
 *   and adds a [Job] if one is not provided as part of the context.
 * - `MainScope()` uses [Dispatchers.Main] for its coroutines and has a [SupervisorJob].
 *
 * **The key part of custom usage of `CoroutineScope` is cancelling it at the end of the lifecycle.**
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
 * This is a shorthand for `CoroutineScope(thisScope.coroutineContext + context)` and can be used as
 * a combinator with existing constructors:
 * ```
 * class MyActivity {
 *     val uiScope = MainScope() + CoroutineName("MyActivity")
 * }
 * ```
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
 * Coroutine cancallation [is cooperative](https://kotlinlang.org/docs/cancellation-and-timeouts.html#cancellation-is-cooperative)
 * and normally, it's checked if a coroutine is cancelled when it *suspends*, for example,
 * when trying to read from a [channel][kotlinx.coroutines.channels.Channel] that is empty.
 *
 * Sometimes, a coroutine does not need to perform suspending operations, but still wants to be cooperative
 * and respect cancellation.
 *
 * The [isActive] property is inteded to be used for scenarios like this:
 * ```
 * val watchdogDispatcher = Dispatchers.IO.limitParallelism(1)
 * fun backgroundWork() {
 *     println("Doing bookkeeping in the background in a non-suspending manner")
 *     Thread.sleep(100L) // Sleep 100ms
 * }
 * // Part of some non-trivial CoroutineScope-confined lifecycle
 * launch(watchdogDispatcher) {
 *     while (isActive) {
 *         // Repetitively do some background work that is non-suspending
 *         backgroundWork()
 *     }
 * }
 * ```
 *
 * This function returns `true` if there is no [job][Job] in the scope's [coroutineContext][CoroutineScope.coroutineContext].
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
 *     coroutineScope {
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
 * The provided scope inherits its [coroutineContext][CoroutineScope.coroutineContext] from the outer scope, using the
 * [Job] from that context as the parent for a new [Job].
 *
 * This function is designed for _concurrent decomposition_ of work. When any child coroutine in this scope fails,
 * this scope fails, cancelling all the other children (for a different behavior, see [supervisorScope]).
 * This function returns as soon as the given block and all its child coroutines are completed.
 * A usage of a scope looks like this:
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
 * The method may throw a [CancellationException] if the current job was cancelled externally,
 * rethrow the exception thrown by [block], or throw an unhandled [Throwable] if there is one
 * (for example, from a crashed coroutine that was started with [launch][CoroutineScope.launch] in this scope).
 */
public suspend fun <R> coroutineScope(block: suspend CoroutineScope.() -> R): R {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    return suspendCoroutineUninterceptedOrReturn { uCont ->
        val coroutine = ScopeCoroutine(uCont.context, uCont)
        @Suppress("LEAKED_IN_PLACE_LAMBDA") // Contract is preserved, invoked immediately or throws
        coroutine.startUndispatchedOrReturn(coroutine, block)
    }
}

/**
 * Creates a [CoroutineScope] that wraps the given coroutine [context].
 *
 * If the given [context] does not contain a [Job] element, then a default `Job()` is created.
 * This way, failure of any child coroutine in this scope or [cancellation][CoroutineScope.cancel] of the scope itself
 * cancels all the scope's children, just like inside [coroutineScope] block.
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
 * Throws the [CancellationException] that was the scope's cancellation cause if the scope is no longer [active][CoroutineScope.isActive].
 *
 * Coroutine cancallation [is cooperative](https://kotlinlang.org/docs/cancellation-and-timeouts.html#cancellation-is-cooperative)
 * and normally, it's checked if a coroutine is cancelled when it *suspends*, for example,
 * when trying to read from a [channel][kotlinx.coroutines.channels.Channel] that is empty.
 *
 * Sometimes, a coroutine does not need to perform suspending operations, but still wants to be cooperative
 * and respect cancellation.
 *
 * [ensureActive] function is inteded to be used for these scenarios and immediately bubble up the cancellation exception:
 * ```
 * val watchdogDispatcher = Dispatchers.IO.limitParallelism(1)
 * fun backgroundWork() {
 *     println("Doing bookkeeping in the background in a non-suspending manner")
 *     Thread.sleep(100L) // Sleep 100ms
 * }
 * fun postBackgroundCleanup() = println("Doing something else")
 * // Part of some non-trivial CoroutineScope-confined lifecycle
 * launch(watchdogDispatcher) {
 *     while (true) {
 *         // Repeatatively do some background work that is non-suspending
 *         backgroundWork()
 *         ensureActive() // Bail out if the scope was cancelled
 *         postBackgroundCleanup() // Won't be invoked if the scope was cancelled
 *     }
 * }
 * ```
 * This function does not do anything if there is no [Job] in the scope's [coroutineContext][CoroutineScope.coroutineContext].
 *
 * @see CoroutineScope.isActive
 * @see CoroutineContext.ensureActive
 */
public fun CoroutineScope.ensureActive(): Unit = coroutineContext.ensureActive()

/**
 * Returns the current [CoroutineContext] retrieved by using [kotlin.coroutines.coroutineContext].
 * This function is an alias to avoid name clash with [CoroutineScope.coroutineContext]:
 *
 * ```
 * // ANTIPATTERN! DO NOT WRITE SUCH A CODE
 * suspend fun CoroutineScope.suspendFunWithScope() {
 *     // Name of the CoroutineScope.coroutineContext in 'this' position, same as `this.coroutineContext`
 *     println(coroutineContext[CoroutineName])
 *     // Name of the context that invoked this suspend function, same as `kotlin.coroutines.coroutineContext`
 *     println(currentCoroutineContext()[CoroutineName])
 * }
 *
 * withContext(CoroutineName("Caller")) {
 *     // Will print 'CoroutineName("Receiver")' and 'CoroutineName("Caller")'
 *     CoroutineScope("Receiver").suspendFunWithScope()
 * }
 * ```
 *
 * This function should always be preferred over [kotlin.coroutines.coroutineContext] property even when there is no explicit clash.
 */
public suspend inline fun currentCoroutineContext(): CoroutineContext = coroutineContext
