/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.scheduling.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.*

private val COROUTINE_ID = AtomicLong()

// for tests only
internal fun resetCoroutineId() {
    COROUTINE_ID.set(0)
}

internal const val COROUTINES_SCHEDULER_PROPERTY_NAME = "kotlinx.coroutines.scheduler"

internal val useCoroutinesScheduler = systemProp(COROUTINES_SCHEDULER_PROPERTY_NAME).let { value ->
    when (value) {
        null, "", "on" -> true
        "off" -> false
        else -> error("System property '$COROUTINES_SCHEDULER_PROPERTY_NAME' has unrecognized value '$value'")
    }
}

internal actual fun createDefaultDispatcher(): CoroutineDispatcher =
    if (useCoroutinesScheduler) DefaultScheduler else CommonPool

/**
 * Creates context for the new coroutine. It installs [Dispatchers.Default] when no other dispatcher nor
 * [ContinuationInterceptor] is specified, and adds optional support for debugging facilities (when turned on).
 *
 * **Debugging facilities:** In debug mode every coroutine is assigned a unique consecutive identifier.
 * Every thread that executes a coroutine has its name modified to include the name and identifier of the
 * currently running coroutine.
 * When one coroutine is suspended and resumes another coroutine that is dispatched in the same thread,
 * then the thread name displays
 * the whole stack of coroutine descriptions that are being executed on this thread.
 *
 * Enable debugging facilities with "`kotlinx.coroutines.debug`" ([DEBUG_PROPERTY_NAME]) system property
 * , use the following values:
 * * "`auto`" (default mode, [DEBUG_PROPERTY_VALUE_AUTO]) -- enabled when assertions are enabled with "`-ea`" JVM option.
 * * "`on`" ([DEBUG_PROPERTY_VALUE_ON]) or empty string -- enabled.
 * * "`off`" ([DEBUG_PROPERTY_VALUE_OFF]) -- disabled.
 *
 * Coroutine name can be explicitly assigned using [CoroutineName] context element.
 * The string "coroutine" is used as a default name.
 *
 * **Note: This is an experimental api.**
 *   Behavior of this function may change in the future with respect to its support for debugging facilities.
 */
@ExperimentalCoroutinesApi
public actual fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext {
    val combined = coroutineContext + context
    val debug = if (DEBUG) combined + CoroutineId(COROUTINE_ID.incrementAndGet()) else combined
    return if (combined !== Dispatchers.Default && combined[ContinuationInterceptor] == null)
        debug + Dispatchers.Default else debug
}

/**
 * Executes a block using a given coroutine context.
 */
internal actual inline fun <T> withCoroutineContext(context: CoroutineContext, countOrElement: Any?, block: () -> T): T {
    val oldValue = updateThreadContext(context, countOrElement)
    try {
        return block()
    } finally {
        restoreThreadContext(context, oldValue)
    }
}

internal actual val CoroutineContext.coroutineName: String? get() {
    if (!DEBUG) return null
    val coroutineId = this[CoroutineId] ?: return null
    val coroutineName = this[CoroutineName]?.name ?: "coroutine"
    return "$coroutineName#${coroutineId.id}"
}

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun CoroutineContext.minusId(): CoroutineContext = minusKey(CoroutineId)

private const val DEBUG_THREAD_NAME_SEPARATOR = " @"

internal data class CoroutineId(
    val id: Long
) : ThreadContextElement<String>, AbstractCoroutineContextElement(CoroutineId) {
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
