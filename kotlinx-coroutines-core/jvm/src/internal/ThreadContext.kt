package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.coroutines.cancellation.CancellationException

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
            state.append(element, element.updateThreadContext(state.context))
        }
        return state
    }

internal actual fun threadContextElements(context: CoroutineContext): Any = context.fold(0, countAll)!!

// countOrElement is pre-cached in dispatched continuation
// returns NO_THREAD_ELEMENTS if the contest does not have any ThreadContextElements
internal fun updateThreadContext(context: CoroutineContext, countOrElement: Any?): Any? {
    @Suppress("NAME_SHADOWING")
    val countOrElement = countOrElement ?: threadContextElements(context)
    @Suppress("IMPLICIT_BOXING_IN_IDENTITY_EQUALS")
    return when {
        countOrElement === 0 -> NO_THREAD_ELEMENTS
        countOrElement is Int -> {
            // Multiple elements case
            try {
                context.fold(ThreadState(context, countOrElement), updateState)
            } catch (e: Throwable) {
                throw ContextElementException(
                    "Exception during multiple ThreadContextElement updates", 
                    e
                )
            }
        }
        else -> {
            // Single element case  
            @Suppress("UNCHECKED_CAST")
            val element = countOrElement as ThreadContextElement<Any?>
            try {
                element.updateThreadContext(context)
            } catch (e: Throwable) {
                throw ContextElementException(
                    "Exception in ThreadContextElement.updateThreadContext for ${element::class.simpleName}",
                    e
                )
            }
        }
    }
}
internal class ContextElementException(
    message: String,
    cause: Throwable
) : CancellationException(message, cause)

internal fun restoreThreadContext(context: CoroutineContext, oldState: Any?) {
    when {
        oldState === NO_THREAD_ELEMENTS -> return
        oldState is ThreadState -> {
            try {
                oldState.restore(context)
            } catch (e: Throwable) {
                throw ContextElementException(
                    "Exception during multiple ThreadContextElement restoration",
                    e
                )
            }
        }
        else -> {
            @Suppress("UNCHECKED_CAST")
            val element = context[oldState as CoroutineContext.Key<Any?>] as ThreadContextElement<Any?>
            try {
                element.restoreThreadContext(context, oldState)
            } catch (e: Throwable) {
                throw ContextElementException(
                    "Exception in ThreadContextElement.restoreThreadContext for ${element::class.simpleName}",
                    e
                )
            }
        }
    }
}

// top-level data class for a nicer out-of-the-box toString representation and class name
@PublishedApi
internal data class ThreadLocalKey(private val threadLocal: ThreadLocal<*>) : CoroutineContext.Key<ThreadLocalElement<*>>

internal class ThreadLocalElement<T>(
    private val value: T,
    private val threadLocal: ThreadLocal<T>
) : ThreadContextElement<T> {
    override val key: CoroutineContext.Key<*> = ThreadLocalKey(threadLocal)

    override fun updateThreadContext(context: CoroutineContext): T {
        val oldState = threadLocal.get()
        threadLocal.set(value)
        return oldState?: -1
    }

    override fun restoreThreadContext(context: CoroutineContext, oldState: T) {
        threadLocal.set(oldState)
    }

    // this method is overridden to perform value comparison (==) on key
    override fun minusKey(key: CoroutineContext.Key<*>): CoroutineContext {
        return if (this.key == key) EmptyCoroutineContext else this
    }

    // this method is overridden to perform value comparison (==) on key
    public override operator fun <E : CoroutineContext.Element> get(key: CoroutineContext.Key<E>): E? =
        @Suppress("UNCHECKED_CAST")
        if (this.key == key) this as E else null

    override fun toString(): String = "ThreadLocal(value=$value, threadLocal = $threadLocal)"
}
