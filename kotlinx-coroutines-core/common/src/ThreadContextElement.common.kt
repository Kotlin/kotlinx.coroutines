package kotlinx.coroutines

import kotlin.coroutines.*

/**
 * Defines elements in [CoroutineContext] that are installed into thread context
 * every time the coroutine with this element in the context is resumed on a thread.
 *
 * In this context, by a "thread" we mean an environment where coroutines are executed in parallel to coroutines
 * other threads.
 * On JVM and Native, this is the same as an operating system thread.
 * On JS, Wasm/JS, and Wasm/WASI, because coroutines can not actually execute in parallel,
 * we say that there is a single thread running all coroutines.
 *
 * Implementations of this interface define a type [S] of the thread-local state that they need to store
 * when the coroutine is resumed and restore later on when it suspends.
 * The coroutines infrastructure provides the corresponding storage.
 *
 * Example usage looks like this:
 *
 * ```
 * // Appends "name" of a coroutine to the current thread name when a coroutine is executed
 * class CoroutineName(val name: String) : ThreadContextElement<String> {
 *     // declare companion object for a key of this element in coroutine context
 *     companion object Key : CoroutineContext.Key<CoroutineName>
 *
 *     // provide the key of the corresponding context element
 *     override val key: CoroutineContext.Key<CoroutineName>
 *         get() = Key
 *
 *     // this is invoked before a coroutine is resumed on the current thread
 *     override fun updateThreadContext(context: CoroutineContext): String {
 *         val previousName = Thread.currentThread().name
 *         Thread.currentThread().name = "$previousName # $name"
 *         return previousName
 *     }
 *
 *     // this is invoked after a coroutine has suspended on the current thread
 *     override fun restoreThreadContext(context: CoroutineContext, oldState: String) {
 *         Thread.currentThread().name = oldState
 *     }
 * }
 *
 * // Usage
 * launch(Dispatchers.Main + CoroutineName("Progress bar coroutine")) { ... }
 * ```
 *
 * Every time this coroutine is resumed on a thread, the name of the thread backing [Dispatchers.Main] is updated to
 * "UI thread original name # Progress bar coroutine", and the thread name is restored to the original one when
 * this coroutine suspends.
 *
 * On JVM, to use a `ThreadLocal` variable within the coroutine, use the `ThreadLocal.asContextElement` function.
 *
 * ### Reentrancy and thread safety
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
     * Updates the context of the current thread.
     *
     * This function is invoked before the coroutine in the specified [context] is started or resumed
     * in the current thread when this element is present in the context of the coroutine.
     * The result of this function is the old value of the thread-local state
     * that will be passed to [restoreThreadContext] when the coroutine eventually suspends or completes.
     * This method should handle its own exceptions and not rethrow them.
     * Thrown exceptions will leave the coroutine whose context is updated in an undefined state
     * and may crash the application.
     *
     * @param context the context of the coroutine that's being started or resumed.
     */
    public fun updateThreadContext(context: CoroutineContext): S

    /**
     * Restores the context of the current thread.
     *
     * This function is invoked after the coroutine in the specified [context] has suspended or finished
     * in the current thread if [updateThreadContext] was previously invoked when this coroutine was started or resumed.
     * [oldState] is the result of the preceding invocation of [updateThreadContext],
     * and this value should be restored in the thread-local state by this function.
     * This method should handle its own exceptions and not rethrow them.
     * Thrown exceptions will leave the coroutine whose context is updated in an undefined state
     * and may crash the application.
     *
     * @param context the context of the coroutine that has suspended or finished.
     * @param oldState the value returned by the preceding invocation of [updateThreadContext].
     */
    public fun restoreThreadContext(context: CoroutineContext, oldState: S)
}

/**
 * A [ThreadContextElement] that is copied whenever a child coroutine inherits a context containing it.
 *
 * [ThreadContextElement] can be used to ensure that when several coroutines share the same thread,
 * they can each have their personal (though immutable) thread-local state without affecting the other coroutines.
 * Often, however, it is desirable to propagate the thread-local state across coroutine suspensions
 * and to child coroutines.
 * A [CopyableThreadContextElement] is an instrument for implementing exactly this kind of
 * hierarchical mutable thread-local state.
 *
 * A change made to a thread-local value with a matching [CopyableThreadContextElement] by a coroutine
 * will be visible to _itself_ (even after the coroutine suspends and subsequently resumes)
 * and any child coroutine launched _after_ that write.
 * Changes introduced to the thread-local value by the parent coroutine _after_ launching a child coroutine
 * will not be visible to that child coroutine.
 * Changes will not be visible to the parent coroutine, peer coroutines, or coroutines that also have
 * this [CopyableThreadContextElement] in their context and simply happen to use the same thread.
 *
 * This can be used to allow a coroutine to use a mutable-thread-local-value-based API transparently and
 * correctly, regardless of the coroutine's structured concurrency.
 *
 * The changes *may* be visible to unrelated coroutines that are launched on the same thread if those coroutines
 * do not have a [CopyableThreadContextElement] with the same key in their context.
 * Because of this, it is an error to access a thread-local value from a coroutine without the corresponding
 * [CopyableThreadContextElement] when other coroutines may have modified it.
 *
 * This example adapts thread-local-value-based method tracing to follow coroutine switches and child coroutine creation.
 * when the tracing happens inside a coroutine:
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
 *         // Copy from the ThreadLocal source of truth at the child coroutine launch time. This makes
 *         // ThreadLocal writes between the resumption of the parent coroutine and the launch of the
 *         // child coroutine visible to the child.
 *         return TraceContextElement(traceThreadLocal.get()?.copy())
 *     }
 *
 *     override fun mergeForChild(overwritingElement: CoroutineContext.Element): CoroutineContext {
 *         // The merge operation defines how to handle situations when both
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
 * A coroutine using this mechanism can safely call coroutine-oblivious code that assumes
 * a specific thread local element's value is installed into the target thread local.
 *
 * ### Reentrancy and thread-safety
 *
 * Correct implementations of this interface must expect that calls to [restoreThreadContext]
 * may happen in parallel to the subsequent [updateThreadContext] and [restoreThreadContext] operations.
 *
 * Even though an element is copied for each child coroutine, an implementation should be able to handle the following
 * interleaving when a coroutine with the corresponding element is launched on a multithreaded dispatcher:
 *
 * ```
 * coroutine.updateThreadContext() // Thread #1
 * ... coroutine body ...
 * // suspension + immediate dispatch happen here
 * coroutine.updateThreadContext() // Thread #2, coroutine is already resumed
 * // ... coroutine body after suspension point on Thread #2 ...
 * coroutine.restoreThreadContext() // Thread #1, is invoked late because Thread #1 is slow
 * coroutine.restoreThreadContext() // Thread #2, may happen in parallel with the previous restore
 * ```
 *
 * All implementations of [CopyableThreadContextElement] should be thread-safe and guard their internal mutable state
 * within an element accordingly.
 */
@DelicateCoroutinesApi
@ExperimentalCoroutinesApi
public interface CopyableThreadContextElement<S> : ThreadContextElement<S> {

    /**
     * Returns the [CopyableThreadContextElement] to replace `this` `CopyableThreadContextElement` in the child
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
     * Returns the [CopyableThreadContextElement] to replace `this` `CopyableThreadContextElement` in the child
     * coroutine's context that is under construction if the added context does contain an element with the same [key].
     *
     * This method is invoked on the original element, accepting as the parameter
     * the element that is supposed to overwrite it.
     */
    public fun mergeForChild(overwritingElement: CoroutineContext.Element): CoroutineContext
}
