/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import internal.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.experimental.*
import kotlinx.coroutines.experimental.scheduling.*

/**
 * Name of the property that control coroutine debugging. See [newCoroutineContext].
 */
public const val DEBUG_PROPERTY_NAME = "kotlinx.coroutines.debug"

/**
 * Automatic debug configuration value for [DEBUG_PROPERTY_NAME]. See [newCoroutineContext].
 */
public const val DEBUG_PROPERTY_VALUE_AUTO = "auto"

/**
 * Debug turned on value for [DEBUG_PROPERTY_NAME]. See [newCoroutineContext].
 */
public const val DEBUG_PROPERTY_VALUE_ON = "on"

/**
 * Debug turned on value for [DEBUG_PROPERTY_NAME]. See [newCoroutineContext].
 */
public const val DEBUG_PROPERTY_VALUE_OFF = "off"

internal val DEBUG = systemProp(DEBUG_PROPERTY_NAME).let { value ->
    when (value) {
        DEBUG_PROPERTY_VALUE_AUTO, null -> CoroutineId::class.java.desiredAssertionStatus()
        DEBUG_PROPERTY_VALUE_ON, "" -> true
        DEBUG_PROPERTY_VALUE_OFF -> false
        else -> error("System property '$DEBUG_PROPERTY_NAME' has unrecognized value '$value'")
    }
}

private val COROUTINE_ID = AtomicLong()

// for tests only
internal fun resetCoroutineId() {
    COROUTINE_ID.set(0)
}

internal const val COROUTINES_SCHEDULER_PROPERTY_NAME = "kotlinx.coroutines.scheduler"

internal val useCoroutinesScheduler = systemProp(COROUTINES_SCHEDULER_PROPERTY_NAME).let { value ->
    when (value) {
        null -> false
        "", "on" -> true
        else -> error("System property '$COROUTINES_SCHEDULER_PROPERTY_NAME' has unrecognized value '$value'")
    }
}

/**
 * This is the default [CoroutineDispatcher] that is used by all standard builders like
 * [launch], [async], etc if no dispatcher nor any other [ContinuationInterceptor] is specified in their context.
 *
 * It is currently equal to [CommonPool], but the value is subject to change in the future.
 */
@Suppress("PropertyName")
public actual val DefaultDispatcher: CoroutineDispatcher =
    if (useCoroutinesScheduler) ExperimentalCoroutineDispatcher() else CommonPool

/**
 * Creates context for the new coroutine. It installs [DefaultDispatcher] when no other dispatcher nor
 * [ContinuationInterceptor] is specified, and adds optional support for debugging facilities (when turned on).
 *
 * **Debugging facilities:** In debug mode every coroutine is assigned a unique consecutive identifier.
 * Every thread that executes a coroutine has its name modified to include the name and identifier of the
 * currently currently running coroutine.
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
 */
@JvmOverloads // for binary compatibility with newCoroutineContext(context: CoroutineContext) version
@Suppress("ACTUAL_FUNCTION_WITH_DEFAULT_ARGUMENTS")
public actual fun newCoroutineContext(context: CoroutineContext, parent: Job? = null): CoroutineContext {
    val debug = if (DEBUG) context + CoroutineId(COROUTINE_ID.incrementAndGet()) else context
    val wp = if (parent == null) debug else debug + parent
    return if (context !== DefaultDispatcher && context[ContinuationInterceptor] == null)
        wp + DefaultDispatcher else wp
}

/**
 * Executes a block using a given coroutine context.
 */
internal actual inline fun <T> withCoroutineContext(context: CoroutineContext, block: () -> T): T {
    val oldName = context.updateThreadContext()
    try {
        return block()
    } finally {
        restoreThreadContext(oldName)
    }
}

@PublishedApi
internal fun CoroutineContext.updateThreadContext(): String? {
    if (!DEBUG) return null
    val coroutineId = this[CoroutineId] ?: return null
    val coroutineName = this[CoroutineName]?.name ?: "coroutine"
    val currentThread = Thread.currentThread()
    val oldName = currentThread.name
    currentThread.name = buildString(oldName.length + coroutineName.length + 10) {
        append(oldName)
        append(" @")
        append(coroutineName)
        append('#')
        append(coroutineId.id)
    }
    return oldName
}

internal actual val CoroutineContext.coroutineName: String? get() {
    if (!DEBUG) return null
    val coroutineId = this[CoroutineId] ?: return null
    val coroutineName = this[CoroutineName]?.name ?: "coroutine"
    return "$coroutineName#${coroutineId.id}"
}

@PublishedApi
internal fun restoreThreadContext(oldName: String?) {
    if (oldName != null) Thread.currentThread().name = oldName
}

private class CoroutineId(val id: Long) : AbstractCoroutineContextElement(CoroutineId) {
    companion object Key : CoroutineContext.Key<CoroutineId>
    override fun toString(): String = "CoroutineId($id)"
}
