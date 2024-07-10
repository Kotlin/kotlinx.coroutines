package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.jvm.*

@JvmField
internal val NO_THREAD_ELEMENTS = Symbol("NO_THREAD_ELEMENTS")

// Used when there are >= 2 active elements in the context
@Suppress("UNCHECKED_CAST")
internal class ThreadState(@JvmField val context: CoroutineContext, n: Int) {
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
internal val findOne =
    fun (found: ThreadContextElement<*>?, element: CoroutineContext.Element): ThreadContextElement<*>? {
        if (found != null) return found
        return element as? ThreadContextElement<*>
    }

// Updates state for ThreadContextElements in the context using the given ThreadState
internal val updateState =
    fun (state: ThreadState, element: CoroutineContext.Element): ThreadState {
        if (element is ThreadContextElement<*>) {
            state.append(element, element.updateThreadContext(state.context))
        }
        return state
    }

internal fun threadContextElements(context: CoroutineContext): Any = context.fold(0, countAll)!!
