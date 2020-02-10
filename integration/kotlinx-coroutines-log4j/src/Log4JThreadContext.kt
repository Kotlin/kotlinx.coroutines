/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.log4j

import kotlinx.coroutines.*
import org.apache.logging.log4j.ThreadContext
import kotlin.coroutines.AbstractCoroutineContextElement
import kotlin.coroutines.CoroutineContext

/**
 * Context element for [CoroutineContext], enabling the use of Log4J 2's [ThreadContext] with coroutines.
 *
 * # Example
 *
 * The following example demonstrates usage of this class. All `assert`s pass. Though this example only uses the mapped
 * diagnostic context, the nested diagnostic context is also supported.
 *
 * ```kotlin
 *  1. runBlocking {
 *  2.   ThreadContext.put("kotlin", "rocks") // Put a value into the ThreadContext
 *  3.
 *  4.   withContext(Log4JThreadContext()) {
 *  5.     assert(ThreadContext.get("kotlin") == "rocks")
 *  6.     logger.info(...)   // The ThreadContext contains the mapping here
 *  7.
 *  8.     ThreadContext.put("kotlin", "is great")
 *  9.     launch(Dispatchers.IO) {
 * 10.       assert(ThreadContext.get("kotlin") == "rocks")
 * 11.     }
 * 12.   }
 * 13. }
 * ```
 * It may be surprising that the [ThreadContext] contains the pair (`"kotlin"`, `"rocks"`) at line 10. However, recall
 * that on line 4, the [CoroutineContext] was updated with the [Log4JThreadContext] element. When, on line 9, a new
 * [CoroutineContext] is forked from [CoroutineContext] created on line 4, the same [Log4JThreadContext] element from
 * line 4 is applied. The [ThreadContext] modification made on line 8 is not part of the [state].
 *
 * ## Combine with other
 * You may wish to combine this [ThreadContextElement] with other [CoroutineContext]s.
 *
 * ```kotlin
 * launch(Dispatchers.IO + Log4JThreadContext()) { ... }
 * ```
 *
 * # CloseableThreadContext
 * [org.apache.logging.log4j.CloseableThreadContext] is useful for automatically cleaning up the [ThreadContext] after a
 * block of code. The structured concurrency provided by coroutines offers the same functionality.
 *
 * In the following example, the modifications to the [ThreadContext] are cleaned up when the coroutine exits.
 *
 * ```kotlin
 * ThreadContext.put("kotlin", "rocks")
 *
 * withContext(Log4JThreadContext()) {
 *   ThreadContext.put("kotlin", "is awesome")
 * }
 * assert(ThreadContext.get("kotlin") == "rocks")
 * ```
 *
 * @param state the values of [ThreadContext]. The default value is a copy of the current state.
 */
public class Log4JThreadContext(
    public val state: Log4JThreadContextState = Log4JThreadContextState()
) : ThreadContextElement<Log4JThreadContextState>, AbstractCoroutineContextElement(Key) {
    /**
     * Key of [Log4JThreadContext] in [CoroutineContext].
     */
    companion object Key : CoroutineContext.Key<Log4JThreadContext>

    /** @suppress */
    override fun updateThreadContext(context: CoroutineContext): Log4JThreadContextState {
        val oldState = Log4JThreadContextState()
        setCurrent(state)
        return oldState
    }

    /** @suppress */
    override fun restoreThreadContext(context: CoroutineContext, oldState: Log4JThreadContextState) {
        setCurrent(oldState)
    }

    private fun setCurrent(state: Log4JThreadContextState) {
        ThreadContext.clearMap()
        ThreadContext.putAll(state.mdc)

        // setStack clears the existing stack
        ThreadContext.setStack(state.ndc)
    }
}

/**
 * Holder for the state of a [ThreadContext].
 *
 * @param mdc a copy of the mapped diagnostic context.
 * @param ndc a copy of the nested diagnostic context.
 */
public class Log4JThreadContextState(
    val mdc: Map<String, String> = ThreadContext.getImmutableContext(),
    val ndc: ThreadContext.ContextStack = ThreadContext.getImmutableStack()
)