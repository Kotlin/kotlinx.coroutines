package kotlinx.coroutines.experimental

import java.util.concurrent.atomic.AtomicLong
import kotlin.coroutines.AbstractCoroutineContextElement
import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext

private const val DEBUG_PROPERTY_NAME = "kotlinx.coroutines.debug"
private val DEBUG = CoroutineId::class.java.desiredAssertionStatus() || System.getProperty(DEBUG_PROPERTY_NAME) != null
private val COROUTINE_ID = AtomicLong()

@PublishedApi
internal val CURRENT_CONTEXT = ThreadLocal<CoroutineContext>()

/**
 * A coroutine dispatcher that executes initial continuation of the coroutine _right here_ in the current call-frame
 * and let the coroutine resume in whatever thread that is used by the corresponding suspending function, without
 * mandating any specific threading policy.
 */
public object Here : CoroutineDispatcher() {
    override fun isDispatchNeeded(): Boolean = false
    override fun dispatch(block: Runnable) { throw UnsupportedOperationException() }
}

/**
 * Creates context for the new coroutine with user-specified overrides from [context] parameter.
 * The [context] for the new coroutine must be explicitly specified and must include [CoroutineDispatcher] element.
 * This function shall be used to start new coroutines.
 *
 * **Debugging facilities:** When assertions are enabled or when "kotlinx.coroutines.debug" system property
 * is set, every coroutine is assigned a unique consecutive identifier. Every thread that executes
 * a coroutine has its name modified to include the name and identifier of the currently currently running coroutine.
 *
 * When one coroutine is suspended and resumes another coroutine in the same thread and a [CoroutineDispatcher]
 * is not explicitly or dispatcher executes continuation in the same thread, then the thread name displays
 * the whole stack of coroutine descriptions that are being executed on this thread.
 *
 * Coroutine name can be explicitly assigned using [CoroutineName] context element.
 * The string "coroutine" is used as a default name.
 */
public fun newCoroutineContext(context: CoroutineContext): CoroutineContext {
    validateContext(context)
    return ((CURRENT_CONTEXT.get() ?: EmptyCoroutineContext) + context).let {
        if (DEBUG) it + CoroutineId(COROUTINE_ID.incrementAndGet()) else it
    }
}

/**
 * Executes a block using a given default coroutine context.
 * This context affects all new coroutines that are started withing the block.
 * The specified [context] is merged onto the current coroutine context (if any).
 */
internal inline fun <T> withDefaultCoroutineContext(context: CoroutineContext, block: () -> T): T {
    val oldContext = CURRENT_CONTEXT.get()
    val oldName = updateContext(oldContext, context)
    try {
        return block()
    } finally {
        restoreContext(oldContext, oldName)
    }
}

private fun validateContext(context: CoroutineContext) {
    check(context[ContinuationInterceptor] is CoroutineDispatcher) {
        "Context of new coroutine must include CoroutineDispatcher"
    }
}

@PublishedApi
internal fun updateContext(oldContext: CoroutineContext?, newContext: CoroutineContext): String? {
    if (newContext === oldContext) return null
    CURRENT_CONTEXT.set(newContext)
    if (!DEBUG) return null
    val newId = newContext[CoroutineId] ?: return null
    val oldId = oldContext?.get(CoroutineId)
    if (newId === oldId) return null
    val currentThread = Thread.currentThread()
    val oldName = currentThread.name
    val coroutineName = newContext[CoroutineName]?.name ?: "coroutine"
    currentThread.name = buildString(oldName.length + coroutineName.length + 10) {
        append(oldName)
        append(" @")
        append(coroutineName)
        append('#')
        append(newId.id)
    }
    return oldName
}

@PublishedApi
internal fun restoreContext(oldContext: CoroutineContext?, oldName: String?) {
    if (oldName != null) Thread.currentThread().name = oldName
    CURRENT_CONTEXT.set(oldContext)
}

private class CoroutineId(val id: Long) : AbstractCoroutineContextElement(CoroutineId) {
    companion object Key : CoroutineContext.Key<CoroutineId>
    override fun toString(): String = "CoroutineId($id)"
}
