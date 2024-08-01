package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*

// countOrElement is pre-cached in dispatched continuation
// returns NO_THREAD_ELEMENTS if the contest does not have any ThreadContextElements
internal fun updateThreadContext(context: CoroutineContext, countOrElement: Any?): Any? {
    @Suppress("NAME_SHADOWING")
    val countOrElement = countOrElement ?: threadContextElements(context)
    @Suppress("IMPLICIT_BOXING_IN_IDENTITY_EQUALS")
    return when {
        countOrElement == 0 -> NO_THREAD_ELEMENTS // very fast path when there are no active ThreadContextElements
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
