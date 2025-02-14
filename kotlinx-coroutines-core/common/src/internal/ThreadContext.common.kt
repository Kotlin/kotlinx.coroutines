package kotlinx.coroutines.internal

import kotlinx.coroutines.ThreadContextElement
import kotlin.coroutines.*
import kotlin.jvm.JvmField

@JvmField
internal val NO_THREAD_ELEMENTS = Symbol("NO_THREAD_ELEMENTS")

// Used when there are >= 2 active elements in the context
@Suppress("UNCHECKED_CAST")
private class ThreadState(@JvmField val context: CoroutineContext, n: Int) {
    private val values = arrayOfNulls<Any>(n)
    private val elements = arrayOfNulls<ThreadContextElement<Any?>>(n)
    private var i = 0

    fun append(element: ThreadContextElement<*>, value: Any?) {
        values[i] = value
        elements[i++] = element as ThreadContextElement<Any?>
    }

    fun restore(context: CoroutineContext) {
        for (i in elements.indices.reversed()) {
            elements[i]!!.restoreThreadContext(context, values[i])
        }
    }
}

// Counts ThreadContextElements in the context
// Any here is Int | ThreadContextElement (when count is one)
private val countAll =
    fun (countOrElement: Any, element: CoroutineContext.Element): Any {
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
            state.append(element, element.updateThreadContext(state.context))
        }
        return state
    }

internal expect fun isZeroCount(countOrElement: Any?): Boolean

// countOrElement is pre-cached in dispatched continuation
// returns NO_THREAD_ELEMENTS if the contest does not have any ThreadContextElements
internal fun updateThreadContext(context: CoroutineContext, countOrElement: Any?): Any? {
    @Suppress("NAME_SHADOWING")
    val countOrElement = countOrElement ?: threadContextElements(context)
    return when {
        isZeroCount(countOrElement) -> NO_THREAD_ELEMENTS // very fast path when there are no active ThreadContextElements
        countOrElement is Int -> {
            // slow path for multiple active ThreadContextElements, allocates ThreadState for multiple old values
            context.fold(ThreadState(context, countOrElement), updateState)
        }
        else -> {
            // fast path for one ThreadContextElement (no allocations, no additional context scan)
            @Suppress("UNCHECKED_CAST")
            val element = countOrElement as ThreadContextElement<Any?>
            element.updateThreadContext(context)
        }
    }
}

internal fun restoreThreadContext(context: CoroutineContext, oldState: Any?) {
    when {
        oldState === NO_THREAD_ELEMENTS -> return // very fast path when there are no ThreadContextElements
        oldState is ThreadState -> {
            // slow path with multiple stored ThreadContextElements
            oldState.restore(context)
        }
        else -> {
            // fast path for one ThreadContextElement, but need to find it
            @Suppress("UNCHECKED_CAST")
            val element = context.fold(null, findOne) as ThreadContextElement<Any?>
            element.restoreThreadContext(context, oldState)
        }
    }
}

internal fun threadContextElements(context: CoroutineContext): Any = context.fold(0, countAll)
