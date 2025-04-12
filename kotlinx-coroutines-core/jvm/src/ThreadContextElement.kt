package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * Wraps [ThreadLocal] into [ThreadContextElement]. The resulting [ThreadContextElement]
 * maintains the given [value] of the given [ThreadLocal] for a coroutine regardless of the actual thread it is resumed on.
 * By default [ThreadLocal.get] is used as a value for the thread-local variable, but it can be overridden with the [value] parameter.
 * Beware that the context element **does not track** modifications of the thread-local and accessing thread-local from a coroutine
 * without the corresponding context element returns an **undefined** value. See the examples for a detailed description.
 *
 *
 * Example usage:
 * ```
 * val myThreadLocal = ThreadLocal<String?>()
 * ...
 * println(myThreadLocal.get()) // Prints "null"
 * launch(Dispatchers.Default + myThreadLocal.asContextElement(value = "foo")) {
 *     println(myThreadLocal.get()) // Prints "foo"
 *     withContext(Dispatchers.Main) {
 *         println(myThreadLocal.get()) // Prints "foo", but it's on UI thread
 *     }
 * }
 * println(myThreadLocal.get()) // Prints "null"
 * ```
 *
 * The context element does not track modifications of the thread-local variable, for example:
 *
 * ```
 * myThreadLocal.set("main")
 * withContext(Dispatchers.Main) {
 *     println(myThreadLocal.get()) // Prints "main"
 *     myThreadLocal.set("UI")
 * }
 * println(myThreadLocal.get()) // Prints "main", not "UI"
 * ```
 *
 * Use `withContext` to update the corresponding thread-local variable to a different value, for example:
 * ```
 * withContext(myThreadLocal.asContextElement("foo")) {
 *     println(myThreadLocal.get()) // Prints "foo"
 * }
 * ```
 *
 * Accessing the thread-local without corresponding context element leads to undefined value:
 * ```
 * val tl = ThreadLocal.withInitial { "initial" }
 *
 * runBlocking {
 *     println(tl.get()) // Will print "initial"
 *     // Change context
 *     withContext(tl.asContextElement("modified")) {
 *         println(tl.get()) // Will print "modified"
 *     }
 *     // Context is changed again
 *     println(tl.get()) // <- WARN: can print either "modified" or "initial"
 * }
 * ```
 * to fix this behaviour use `runBlocking(tl.asContextElement())`
 */
public fun <T> ThreadLocal<T>.asContextElement(value: T = get()): ThreadContextElement<T> =
    ThreadLocalElement(value, this)

/**
 * Return `true` when current thread local is present in the coroutine context, `false` otherwise.
 * Thread local can be present in the context only if it was added via [asContextElement] to the context.
 *
 * Example of usage:
 * ```
 * suspend fun processRequest() {
 *     if (traceCurrentRequestThreadLocal.isPresent()) { // Probabilistic tracing
 *         // Do some heavy-weight tracing
 *     }
 *     // Process request regularly
 * }
 * ```
 */
public suspend inline fun ThreadLocal<*>.isPresent(): Boolean = coroutineContext[ThreadLocalKey(this)] !== null

/**
 * Checks whether current thread local is present in the coroutine context and throws [IllegalStateException] if it is not.
 * It is a good practice to validate that thread local is present in the context, especially in large code-bases,
 * to avoid stale thread-local values and to have a strict invariants.
 *
 * E.g. one may use the following method to enforce proper use of the thread locals with coroutines:
 * ```
 * public suspend inline fun <T> ThreadLocal<T>.getSafely(): T {
 *     ensurePresent()
 *     return get()
 * }
 *
 * // Usage
 * withContext(...) {
 *     val value = threadLocal.getSafely() // Fail-fast in case of improper context
 * }
 * ```
 */
public suspend inline fun ThreadLocal<*>.ensurePresent(): Unit =
    check(isPresent()) { "ThreadLocal $this is missing from context $coroutineContext" }
