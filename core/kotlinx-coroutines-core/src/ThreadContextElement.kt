/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.internal.*
import kotlin.coroutines.experimental.*

/**
 * Defines elements in [CoroutineContext] that are installed into thread context
 * every time the coroutine with this element in the context is resumed on a thread.
 *
 * Implementations of this interface define a type [S] of the thread-local state that they need to store on
 * resume of a coroutine and restore later on suspend and the infrastructure provides the corresponding storage.
 *
 * Example usage looks like this:
 *
 * ```
 * // declare thread local variable holding MyData
 * private val myThreadLocal = ThreadLocal<MyData?>()
 *
 * // declare context element holding MyData
 * class MyElement(val data: MyData) : ThreadContextElement<MyData?> {
 *     // declare companion object for a key of this element in coroutine context
 *     companion object Key : CoroutineContext.Key<MyElement>
 *
 *     // provide the key of the corresponding context element
 *     override val key: CoroutineContext.Key<MyElement>
 *         get() = Key
 *
 *     // this is invoked before coroutine is resumed on current thread
 *     override fun updateThreadContext(context: CoroutineContext): MyData? {
 *         val oldState = myThreadLocal.get()
 *         myThreadLocal.set(data)
 *         return oldState
 *     }
 *
 *     // this is invoked after coroutine has suspended on current thread
 *     override fun restoreThreadContext(context: CoroutineContext, oldState: MyData?) {
 *         myThreadLocal.set(oldState)
 *     }
 * }
 * ```
 */
public interface ThreadContextElement<S> : CoroutineContext.Element {
    /**
     * Updates context of the current thread.
     * This function is invoked before the coroutine in the specified [context] is resumed in the current thread
     * when the context of the coroutine this element.
     * The result of this function is the old value of the thread-local state that will be passed to [restoreThreadContext].
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
     *
     * @param context the coroutine context.
     * @param oldState the value returned by the previous invocation of [updateThreadContext].
     */
    public fun restoreThreadContext(context: CoroutineContext, oldState: S)
}

private val ZERO = Symbol("ZERO")

// Used when there are >= 2 active elements in the context
private class ThreadState(val context: CoroutineContext, n: Int) {
    private var a = arrayOfNulls<Any>(n)
    private var i = 0

    fun append(value: Any?) { a[i++] = value }
    fun take() = a[i++]
    fun start() { i = 0 }
}

// Counts ThreadContextElements in the context
// Any? here is Int | ThreadContextElement (when count is one)
private val countAll =
    fun (countOrElement: Any?, element: CoroutineContext.Element): Any? {
        if (element is ThreadContextElement<*>) {
            val inCount = countOrElement as? Int ?: 1
            return if (inCount == 0) element else inCount + 1
        }
        return countOrElement
    }

// Find one (first) ThreadContextElement in the context, it is used when we know there is exactly one
private val findOne =
    fun (found: ThreadContextElement<*>?, element: CoroutineContext.Element): ThreadContextElement<*>? {
        if (found != null) return found
        return element as? ThreadContextElement<*>
    }

// Updates state for ThreadContextElements in the context using the given ThreadState
private val updateState =
    fun (state: ThreadState, element: CoroutineContext.Element): ThreadState {
        if (element is ThreadContextElement<*>) {
            state.append(element.updateThreadContext(state.context))
        }
        return state
    }

// Restores state for all ThreadContextElements in the context from the given ThreadState
private val restoreState =
    fun (state: ThreadState, element: CoroutineContext.Element): ThreadState {
        @Suppress("UNCHECKED_CAST")
        if (element is ThreadContextElement<*>) {
            (element as ThreadContextElement<Any?>).restoreThreadContext(state.context, state.take())
        }
        return state
    }

internal fun updateThreadContext(context: CoroutineContext): Any? {
    val count = context.fold(0, countAll)
    @Suppress("IMPLICIT_BOXING_IN_IDENTITY_EQUALS")
    return when {
        count === 0 -> ZERO // very fast path when there are no active ThreadContextElements
        //    ^^^ identity comparison for speed, we know zero always has the same identity
        count is Int -> {
            // slow path for multiple active ThreadContextElements, allocates ThreadState for multiple old values
            context.fold(ThreadState(context, count), updateState)
        }
        else -> {
            // fast path for one ThreadContextElement (no allocations, no additional context scan)
            @Suppress("UNCHECKED_CAST")
            val element = count as ThreadContextElement<Any?>
            element.updateThreadContext(context)
        }
    }
}

internal fun restoreThreadContext(context: CoroutineContext, oldState: Any?) {
    when {
        oldState === ZERO -> return // very fast path when there are no ThreadContextElements
        oldState is ThreadState -> {
            // slow path with multiple stored ThreadContextElements
            oldState.start()
            context.fold(oldState, restoreState)
        }
        else -> {
            // fast path for one ThreadContextElement, but need to find it
            @Suppress("UNCHECKED_CAST")
            val element = context.fold(null, findOne) as ThreadContextElement<Any?>
            element.restoreThreadContext(context, oldState)
        }
    }
}
