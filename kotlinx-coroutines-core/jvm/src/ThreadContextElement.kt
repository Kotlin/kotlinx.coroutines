/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * Defines elements in [CoroutineContext] that are installed into thread context
 * every time the coroutine with this element in the context is resumed on a thread.
 *
 * Implementations of this interface define a type [S] of the thread-local state that they need to store on
 * resume of a coroutine and restore later on suspend. The infrastructure provides the corresponding storage.
 *
 * Example usage looks like this:
 *
 * ```
 * // Appends "name" of a coroutine to a current thread name when coroutine is executed
 * class CoroutineName(val name: String) : ThreadContextElement<String> {
 *     // declare companion object for a key of this element in coroutine context
 *     companion object Key : CoroutineContext.Key<CoroutineName>
 *
 *     // provide the key of the corresponding context element
 *     override val key: CoroutineContext.Key<CoroutineName>
 *         get() = Key
 *
 *     // this is invoked before coroutine is resumed on current thread
 *     override fun updateThreadContext(context: CoroutineContext): String {
 *         val previousName = Thread.currentThread().name
 *         Thread.currentThread().name = "$previousName # $name"
 *         return previousName
 *     }
 *
 *     // this is invoked after coroutine has suspended on current thread
 *     override fun restoreThreadContext(context: CoroutineContext, oldState: String) {
 *         Thread.currentThread().name = oldState
 *     }
 * }
 *
 * // Usage
 * launch(Dispatchers.Main + CoroutineName("Progress bar coroutine")) { ... }
 * ```
 *
 * Every time this coroutine is resumed on a thread, UI thread name is updated to
 * "UI thread original name # Progress bar coroutine" and the thread name is restored to the original one when
 * this coroutine suspends.
 *
 * To use [ThreadLocal] variable within the coroutine use [ThreadLocal.asContextElement][asContextElement] function.
 */
public interface ThreadContextElement<S> : CoroutineContext.Element {
    /**
     * Updates context of the current thread.
     * This function is invoked before the coroutine in the specified [context] is resumed in the current thread
     * when the context of the coroutine this element.
     * The result of this function is the old value of the thread-local state that will be passed to [restoreThreadContext].
     * This method should handle its own exceptions and do not rethrow it. Thrown exceptions will leave coroutine which
     * context is updated in an undefined state and may crash an application.
     *
     * @param context the coroutine context.
     */
    public fun updateThreadContext(context: CoroutineContext): S

    /**
     * Restores context of the current thread.
     * This function is invoked after the coroutine in the specified [context] is suspended in the current thread
     * if [updateThreadContext] was previously invoked on resume of this coroutine.
     * The value of [oldState] is the result of the previous invocation of [updateThreadContext] and it should
     * be restored in the thread-local state by this function.
     * This method should handle its own exceptions and do not rethrow it. Thrown exceptions will leave coroutine which
     * context is updated in an undefined state and may crash an application.
     *
     * @param context the coroutine context.
     * @param oldState the value returned by the previous invocation of [updateThreadContext].
     */
    public fun restoreThreadContext(context: CoroutineContext, oldState: S)
}

/**
 * Wraps [ThreadLocal] into [ThreadContextElement]. The resulting [ThreadContextElement]
 * maintains the given [value] of the given [ThreadLocal] for coroutine regardless of the actual thread its is resumed on.
 * By default [ThreadLocal.get] is used as a value for the thread-local variable, but it can be overridden with [value] parameter.
 * Beware that context element **does not track** modifications of the thread-local and accessing thread-local from coroutine
 * without the corresponding context element returns **undefined** value. See the examples for a detailed description.
 *
 *
 * Example usage:
 * ```
 * val myThreadLocal = ThreadLocal<String?>()
 * ...
 * println(myThreadLocal.get()) // Prints "null"
 * launch(Dispatchers.Default + myThreadLocal.asContextElement(value = "foo")) {
 *   println(myThreadLocal.get()) // Prints "foo"
 *   withContext(Dispatchers.Main) {
 *     println(myThreadLocal.get()) // Prints "foo", but it's on UI thread
 *   }
 * }
 * println(myThreadLocal.get()) // Prints "null"
 * ```
 *
 * The context element does not track modifications of the thread-local variable, for example:
 *
 * ```
 * myThreadLocal.set("main")
 * withContext(Dispatchers.Main) {
 *   println(myThreadLocal.get()) // Prints "main"
 *   myThreadLocal.set("UI")
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
 *   println(tl.get()) // Will print "initial"
 *   // Change context
 *   withContext(tl.asContextElement("modified")) {
 *     println(tl.get()) // Will print "modified"
 *   }
 *   // Context is changed again
 *    println(tl.get()) // <- WARN: can print either "modified" or "initial"
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
 *   if (traceCurrentRequestThreadLocal.isPresent()) { // Probabilistic tracing
 *      // Do some heavy-weight tracing
 *   }
 *   // Process request regularly
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
 *   ensurePresent()
 *   return get()
 * }
 *
 * // Usage
 * withContext(...) {
 *   val value = threadLocal.getSafely() // Fail-fast in case of improper context
 * }
 * ```
 */
public suspend inline fun ThreadLocal<*>.ensurePresent(): Unit =
    check(isPresent()) { "ThreadLocal $this is missing from context $coroutineContext" }
