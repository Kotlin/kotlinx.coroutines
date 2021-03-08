/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.log4j2

import kotlinx.coroutines.*
import org.apache.logging.log4j.ThreadContext
import kotlin.coroutines.AbstractCoroutineContextElement
import kotlin.coroutines.CoroutineContext

/**
 * The value of [ThreadContext] context map.
 * See [ThreadContext.getContext].
 */
public typealias MDCContextMap = Map<String, String>?

/**
 * [ThreadContext] context element for [CoroutineContext].
 *
 * Example:
 *
 * ```
 * ThreadContext.put("kotlin", "rocks") // Put a value into the MDC context
 *
 * launch(MDCContext()) {
 *     logger.info { "..." }   // The MDC context contains the mapping here
 * }
 * ```
 *
 * Note that you cannot update MDC context from inside of the coroutine simply
 * using [ThreadContext.put]. These updates are going to be lost on the next suspension and
 * reinstalled to the ThreadContext that was captured or explicitly specified in
 * [contextMap] when this object was created on the next resumption.
 * Use `withContext(MDCContext()) { ... }` to capture updated map of MDC keys and values
 * for the specified block of code.
 *
 * @param contextMap the value of [ThreadContext] context map.
 * Default value is the copy of the current thread's context map that is acquired via
 * [ThreadContext.getContext].
 */
public class MDCContext(
    /**
     * The value of [ThreadContext] context map.
     */
    public val contextMap: MDCContextMap = ThreadContext.getContext()
) : ThreadContextElement<MDCContextMap>, AbstractCoroutineContextElement(Key) {
    /**
     * Key of [MDCContext] in [CoroutineContext].
     */
    public companion object Key : CoroutineContext.Key<MDCContext>

    override fun updateThreadContext(context: CoroutineContext): MDCContextMap {
        val oldState = ThreadContext.getImmutableContext()
        setCurrent(contextMap)
        return oldState
    }

    override fun restoreThreadContext(context: CoroutineContext, oldState: MDCContextMap) {
        setCurrent(oldState)
    }

    private fun setCurrent(contextMap: MDCContextMap) {
        ThreadContext.clearMap()
        if (contextMap != null) {
            ThreadContext.putAll(contextMap)
        }
    }
}
