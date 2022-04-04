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
 * A [ThreadContextElement] copied whenever a child coroutine inherits a context containing it.
 *
 * When an API uses a _mutable_ [ThreadLocal] for consistency, a [CopyableThreadContextElement]
 * can give coroutines "coroutine-safe" write access to that `ThreadLocal`.
 *
 * A write made to a `ThreadLocal` with a matching [CopyableThreadContextElement] by a coroutine
 * will be visible to _itself_ and any child coroutine launched _after_ that write.
 *
 * Writes will not be visible to the parent coroutine, peer coroutines, or coroutines that happen
 * to use the same thread. Writes made to the `ThreadLocal` by the parent coroutine _after_
 * launching a child coroutine will not be visible to that child coroutine.
 *
 * This can be used to allow a coroutine to use a mutable ThreadLocal API transparently and
 * correctly, regardless of the coroutine's structured concurrency.
 *
 * This example adapts a `ThreadLocal` method trace to be "coroutine local" while the method trace
 * is in a coroutine:
 *
 * ```
 * class TraceContextElement(private val traceData: TraceData?) : CopyableThreadContextElement<TraceData?> {
 *     companion object Key : CoroutineContext.Key<TraceContextElement>
 *
 *     override val key: CoroutineContext.Key<TraceContextElement> = Key
 *
 *     override fun updateThreadContext(context: CoroutineContext): TraceData? {
 *         val oldState = traceThreadLocal.get()
 *         traceThreadLocal.set(traceData)
 *         return oldState
 *     }
 *
 *     override fun restoreThreadContext(context: CoroutineContext, oldState: TraceData?) {
 *         traceThreadLocal.set(oldState)
 *     }
 *
 *     override fun copyForChild(): TraceContextElement {
 *         // Copy from the ThreadLocal source of truth at child coroutine launch time. This makes
 *         // ThreadLocal writes between resumption of the parent coroutine and the launch of the
 *         // child coroutine visible to the child.
 *         return TraceContextElement(traceThreadLocal.get()?.copy())
 *     }
 *
 *     override fun mergeForChild(overwritingElement: CoroutineContext.Element): CoroutineContext {
 *         // Merge operation defines how to handle situations when both
 *         // the parent coroutine has an element in the context and
 *         // an element with the same key was also
 *         // explicitly passed to the child coroutine.
 *         // If merging does not require special behavior,
 *         // the copy of the element can be returned.
 *         return TraceContextElement(traceThreadLocal.get()?.copy())
 *     }
 * }
 * ```
 *
 * A coroutine using this mechanism can safely call Java code that assumes the corresponding thread local element's
 * value is installed into the target thread local.
 */
@DelicateCoroutinesApi
@ExperimentalCoroutinesApi
public interface CopyableThreadContextElement<S> : ThreadContextElement<S> {

    /**
     * Returns a [CopyableThreadContextElement] to replace `this` `CopyableThreadContextElement` in the child
     * coroutine's context that is under construction if the added context does not contain an element with the same [key].
     *
     * This function is called on the element each time a new coroutine inherits a context containing it,
     * and the returned value is folded into the context given to the child.
     *
     * Since this method is called whenever a new coroutine is launched in a context containing this
     * [CopyableThreadContextElement], implementations are performance-sensitive.
     */
    public fun copyForChild(): CopyableThreadContextElement<S>

    /**
     * Returns a [CopyableThreadContextElement] to replace `this` `CopyableThreadContextElement` in the child
     * coroutine's context that is under construction if the added context does contain an element with the same [key].
     *
     * This method is invoked on the original element, accepting as the parameter
     * the element that is supposed to overwrite it.
     */
    public fun mergeForChild(overwritingElement: CoroutineContext.Element): CoroutineContext
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
