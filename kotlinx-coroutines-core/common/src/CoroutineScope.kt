/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlin.coroutines.intrinsics.*
import kotlin.coroutines.*

/**
 * Defines a scope for new coroutines. Every coroutine builder
 * is an extension on [CoroutineScope] and inherits its [coroutineContext][CoroutineScope.coroutineContext]
 * to automatically propagate both context elements and cancellation.
 *
 * Every coroutine builder (like [launch][CoroutineScope.launch], [async][CoroutineScope.async], etc)
 * and every scoping function (like [coroutineScope], [withContext], etc) provides _its own_ scope
 * with its own [Job] instance into the inner block of code it runs.
 * By convention, they all wait for all the coroutines inside
 * their block to complete before completing themselves, thus enforcing the
 * discipline of **structured concurrency**.
 *
 * [CoroutineScope] should be implemented on entities with well-defined lifecycle that are responsible
 * for launching children coroutines. Example of such entity on Android is Activity.
 * Usage of this interface may look like this:
 *
 * ```
 * class MyActivity : AppCompatActivity(), CoroutineScope {
 *     lateinit var job: Job
 *     override val coroutineContext: CoroutineContext
 *         get() = Dispatchers.Main + job
 *
 *     override fun onCreate(savedInstanceState: Bundle?) {
 *         super.onCreate(savedInstanceState)
 *         job = Job()
 *     }
 *
 *     override fun onDestroy() {
 *         super.onDestroy()
 *         job.cancel() // Cancel job on activity destroy. After destroy all children jobs will be cancelled automatically
 *     }
 *
 *     /*
 *      * Note how coroutine builders are scoped: if activity is destroyed or any of the launched coroutines
 *      * in this method throws an exception, then all nested coroutines are cancelled.
 *      */
 *     fun loadDataFromUI() = launch { // <- extension on current activity, launched in the main thread
 *        val ioData = async(Dispatchers.IO) { // <- extension on launch scope, launched in IO dispatcher
 *            // blocking I/O operation
 *        }
 *        // do something else concurrently with I/O
 *        val data = ioData.await() // wait for result of I/O
 *        draw(data) // can draw in the main thread
 *     }
 * }
 *
 * ```
 */
public interface CoroutineScope {
    /**
     * Context of this scope.
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
 *   private val scope = MainScope()
 *
 *   override fun onDestroy() {
 *     super.onDestroy()
 *     scope.cancel()
 *   }
 * }
 *
 * ```
 *
 * The resulting scope has [SupervisorJob] and [Dispatchers.Main] context elements.
 * If you want to append additional elements to the main scope, use [CoroutineScope.plus] operator:
 * `val scope = MainScope() + CoroutineName("MyActivity")`.
 */
@Suppress("FunctionName")
@ExperimentalCoroutinesApi // Experimental since 1.1.0, tentatively until 1.2.0
public fun MainScope(): CoroutineScope = ContextScope(SupervisorJob() + Dispatchers.Main)

/**
 * Returns `true` when current [Job] is still active (has not completed and was not cancelled yet).
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
 *
 * Global scope is used to launch top-level coroutines which are operating on the whole application lifetime
 * and are not cancelled prematurely.
 * Another use of the global scope is operators running in [Dispatchers.Unconfined], which don't have any job associated with them.
 *
 * Application code usually should use application-defined [CoroutineScope], using
 * [async][CoroutineScope.async] or [launch][CoroutineScope.launch]
 * on the instance of [GlobalScope] is highly discouraged.
 *
 * Usage of this interface may look like this:
 *
 * ```
 * fun ReceiveChannel<Int>.sqrt(): ReceiveChannel<Double> = GlobalScope.produce(Dispatchers.Unconfined) {
 *     for (number in this) {
 *         send(Math.sqrt(number))
 *     }
 * }
 *
 * ```
 */
public object GlobalScope : CoroutineScope {
    /**
     * Returns [EmptyCoroutineContext].
     */
    override val coroutineContext: CoroutineContext
        get() = EmptyCoroutineContext
}

/**
 * Creates new [CoroutineScope] and calls the specified suspend block with this scope.
 * The provided scope inherits its [coroutineContext][CoroutineScope.coroutineContext] from the outer scope, but overrides
 * context's [Job].
 *
 * This function is designed for a _parallel decomposition_ of work. When any child coroutine in this scope fails,
 * this scope fails and all the rest of the children are cancelled (for a different behavior see [supervisorScope]).
 * This function returns as soon as given block and all its children coroutines are completed.
 * Example of the scope usages looks like this:
 *
 * ```
 * suspend fun loadDataForUI() = coroutineScope {
 *
 *   val data = async { // <- extension on current scope
 *      ... load some UI data ...
 *   }
 *
 *   withContext(Dispatchers.Main) {
 *     doSomeWork()
 *     val result = data.await()
 *     display(result)
 *   }
 * }
 * ```
 *
 * Semantics of the scope in this example:
 * 1) `loadDataForUI` returns as soon as data is loaded and UI is updated.
 * 2) If `doSomeWork` throws an exception, then `async` task is cancelled and `loadDataForUI` rethrows that exception.
 * 3) If outer scope of `loadDataForUI` is cancelled, both started `async` and `withContext` are cancelled.
 *
 * Method may throw [CancellationException] if the current job was cancelled externally
 * or may throw the corresponding unhandled [Throwable] if there is any unhandled exception in this scope
 * (for example, from a crashed coroutine that was started with [launch][CoroutineScope.launch] in this scope).
 */
public suspend fun <R> coroutineScope(block: suspend CoroutineScope.() -> R): R =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        val coroutine = ScopeCoroutine(uCont.context, uCont)
        coroutine.startUndispatchedOrReturn(coroutine, block)
    }

/**
 * Creates [CoroutineScope] that wraps the given coroutine [context].
 *
 * If the given [context] does not contain a [Job] element, then a default `Job()` is created.
 * This way, cancellation or failure or any child coroutine in this scope cancels all the other children,
 * just like inside [coroutineScope] block.
 */
@Suppress("FunctionName")
public fun CoroutineScope(context: CoroutineContext): CoroutineScope =
    ContextScope(if (context[Job] != null) context else context + Job())

/**
 * Cancels this scope, including its job and all its children.
 * Throws [IllegalStateException] if the scope does not have a job in it.
 *
 * This API is experimental in order to investigate possible clashes with other cancellation mechanisms.
 */
@Suppress("NOTHING_TO_INLINE")
@ExperimentalCoroutinesApi // Experimental and inline since 1.1.0, tentatively until 1.2.0
public inline fun CoroutineScope.cancel() {
    val job = coroutineContext[Job] ?: error("Scope cannot be cancelled because it does not have a job: $this")
    job.cancel()
}
