/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import java.util.concurrent.atomic.AtomicLong
import kotlin.coroutines.experimental.AbstractCoroutineContextElement
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.CoroutineContext

private const val DEBUG_PROPERTY_NAME = "kotlinx.coroutines.debug"

private val DEBUG = run {
    val value = try { System.getProperty(DEBUG_PROPERTY_NAME) }
        catch (e: SecurityException) { null }
    when (value) {
        "auto", null -> CoroutineId::class.java.desiredAssertionStatus()
        "on", "" -> true
        "off" -> false
        else -> error("System property '$DEBUG_PROPERTY_NAME' has unrecognized value '$value'")
    }
}

private val COROUTINE_ID = AtomicLong()

// for tests only
internal fun resetCoroutineId() {
    COROUTINE_ID.set(0)
}

/**
 * A coroutine dispatcher that is not confined to any specific thread.
 * It executes initial continuation of the coroutine _right here_ in the current call-frame
 * and let the coroutine resume in whatever thread that is used by the corresponding suspending function, without
 * mandating any specific threading policy.
 *
 * Note, that if you need your coroutine to be confined to a particular thread or a thread-pool after resumption,
 * but still want to execute it in the current call-frame until its first suspension, then you can use
 * an optional [CoroutineStart] parameter in coroutine builders like [launch] and [async] setting it to the
 * the value of [CoroutineStart.UNDISPATCHED].
 */
public actual object Unconfined : CoroutineDispatcher() {
    actual override fun isDispatchNeeded(context: CoroutineContext): Boolean = false
    actual override fun dispatch(context: CoroutineContext, block: Runnable) { throw UnsupportedOperationException() }
    override fun toString(): String = "Unconfined"
}

/**
 * @suppress **Deprecated**: `Here` was renamed to `Unconfined`.
 */
@Deprecated(message = "`Here` was renamed to `Unconfined`",
        replaceWith = ReplaceWith(expression = "Unconfined"))
public typealias Here = Unconfined

/**
 * This is the default [CoroutineDispatcher] that is used by all standard builders like
 * [launch], [async], etc if no dispatcher nor any other [ContinuationInterceptor] is specified in their context.
 *
 * It is currently equal to [CommonPool], but the value is subject to change in the future.
 */
@Suppress("PropertyName")
public actual val DefaultDispatcher: CoroutineDispatcher = CommonPool

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
 * Enable debugging facilities with "`kotlinx.coroutines.debug`" system property, use the following values:
 * * "`auto`" (default mode) -- enabled when assertions are enabled with "`-ea`" JVM option.
 * * "`on`" or empty string -- enabled.
 * * "`off`" -- disabled.
 *
 * Coroutine name can be explicitly assigned using [CoroutineName] context element.
 * The string "coroutine" is used as a default name.
 */
@JvmOverloads // for binary compatibility with newCoroutineContext(context: CoroutineContext) version
public fun newCoroutineContext(context: CoroutineContext, parent: Job? = null): CoroutineContext {
    val debug = if (DEBUG) context + CoroutineId(COROUTINE_ID.incrementAndGet()) else context
    val wp = if (parent == null) debug else debug + parent
    return if (context !== DefaultDispatcher && context[ContinuationInterceptor] == null)
        wp + DefaultDispatcher else wp
}

/**
 * Executes a block using a given coroutine context.
 */
internal inline fun <T> withCoroutineContext(context: CoroutineContext, block: () -> T): T {
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

internal val CoroutineContext.coroutineName: String? get() {
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
