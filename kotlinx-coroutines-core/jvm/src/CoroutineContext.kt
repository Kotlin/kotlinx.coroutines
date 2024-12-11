package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.CoroutineStackFrame

/**
 *  Adds optional support for debugging facilities (when turned on)
 *  and copyable-thread-local facilities on JVM.
 *  See [DEBUG_PROPERTY_NAME] for description of debugging facilities on JVM.
 */
internal actual fun wrapContextWithDebug(context: CoroutineContext): CoroutineContext =
    if (DEBUG) context + CoroutineId(COROUTINE_ID.incrementAndGet()) else context

internal actual val CoroutineContext.coroutineName: String? get() {
    if (!DEBUG) return null
    val coroutineId = this[CoroutineId] ?: return null
    val coroutineName = this[CoroutineName]?.name ?: "coroutine"
    return "$coroutineName#${coroutineId.id}"
}

private const val DEBUG_THREAD_NAME_SEPARATOR = " @"

@IgnoreJreRequirement // desugared hashcode implementation
@PublishedApi
internal data class CoroutineId(
    // Used by the IDEA debugger via reflection and must be kept binary-compatible, see KTIJ-24102
    val id: Long
) : ThreadContextElement<String>, AbstractCoroutineContextElement(CoroutineId) {
    // Used by the IDEA debugger via reflection and must be kept binary-compatible, see KTIJ-24102
    companion object Key : CoroutineContext.Key<CoroutineId>
    override fun toString(): String = "CoroutineId($id)"

    override fun updateThreadContext(context: CoroutineContext): String {
        val coroutineName = context[CoroutineName]?.name ?: "coroutine"
        val currentThread = Thread.currentThread()
        val oldName = currentThread.name
        var lastIndex = oldName.lastIndexOf(DEBUG_THREAD_NAME_SEPARATOR)
        if (lastIndex < 0) lastIndex = oldName.length
        currentThread.name = buildString(lastIndex + coroutineName.length + 10) {
            append(oldName.substring(0, lastIndex))
            append(DEBUG_THREAD_NAME_SEPARATOR)
            append(coroutineName)
            append('#')
            append(id)
        }
        return oldName
    }

    override fun restoreThreadContext(context: CoroutineContext, oldState: String) {
        Thread.currentThread().name = oldState
    }
}
