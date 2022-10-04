/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.slf4j

import kotlinx.coroutines.*
import org.slf4j.MDC
import kotlin.coroutines.AbstractCoroutineContextElement
import kotlin.coroutines.CoroutineContext

/**
 * The value of [MDC] context map.
 * See [MDC.getCopyOfContextMap].
 */
public typealias MDCContextMap = Map<String, String>?

/**
 * [MDC] context element for [CoroutineContext].
 *
 * Example:
 *
 * ```
 * MDC.put("kotlin", "rocks") // Put a value into the MDC context
 *
 * launch(MDCContext()) {
 *     logger.info { "..." }   // The MDC context contains the mapping here
 * }
 * ```
 *
 * Note that you cannot update MDC context from inside the coroutine simply
 * using [MDC.put]. These updates are going to be lost on the next suspension and
 * reinstalled to the MDC context that was captured or explicitly specified in
 * [contextMap] when this object was created on the next resumption.
 * Use `withContext(MDCContext()) { ... }` to capture updated map of MDC keys and values
 * for the specified block of code.
 *
 * @param contextMap the value of [MDC] context map.
 * Default value is the copy of the current thread's context map that is acquired via
 * [MDC.getCopyOfContextMap].
 */
public class MDCContext(
    /**
     * The value of [MDC] context map.
     */
    @Suppress("MemberVisibilityCanBePrivate")
    public val contextMap: MDCContextMap = MDC.getCopyOfContextMap()
) : ThreadContextElement<MDCContextMap>, AbstractCoroutineContextElement(Key) {
    /**
     * Key of [MDCContext] in [CoroutineContext].
     */
    public companion object Key : CoroutineContext.Key<MDCContext>

    /** @suppress */
    override fun updateThreadContext(context: CoroutineContext): MDCContextMap {
        val oldState = MDC.getCopyOfContextMap()
        setCurrent(contextMap)
        return oldState
    }

    /** @suppress */
    override fun restoreThreadContext(context: CoroutineContext, oldState: MDCContextMap) {
        setCurrent(oldState)
    }

    private fun setCurrent(contextMap: MDCContextMap) {
        if (contextMap == null) {
            MDC.clear()
        } else {
            MDC.setContextMap(contextMap)
        }
    }
}
