package kotlinx.coroutines

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
 *
 * ### Reentrancy and thread-safety
 *
 * Correct implementations of this interface must expect that calls to [restoreThreadContext]
 * may happen in parallel to the subsequent [updateThreadContext] and [restoreThreadContext] operations.
 * See [CopyableThreadContextElement] for advanced interleaving details.
 *
 * All implementations of [ThreadContextElement] should be thread-safe and guard their internal mutable state
 * within an element accordingly.
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
