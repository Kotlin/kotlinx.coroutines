/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.log4j

import kotlinx.coroutines.ThreadContextElement
import org.apache.logging.log4j.ThreadContext
import kotlin.coroutines.AbstractCoroutineContextElement
import kotlin.coroutines.CoroutineContext

/**
 * Creates a new, immutable, [DiagnosticContext].
 *
 * See [DiagnosticContext] for usage instructions.
 *
 * If not modifying the [ThreadContext], this method is preferred over [MutableDiagnosticContext] as it performs fewer
 * unnecessary allocations.
 */
public fun immutableDiagnosticContext(): DiagnosticContext = DiagnosticContext(ThreadContext.getImmutableContext())

/**
 * Enables the use of Log4J 2's [ThreadContext] with coroutines.
 *
 * See [DiagnosticContext] for usage instructions.
 *
 * @param mappedContext Mapped diagnostic context to apply for the duration of the corresponding [CoroutineContext].
 */
public class MutableDiagnosticContext private constructor(
    // Local reference so we can mutate the state
    private val mappedContext: MutableMap<String, String?>
) : DiagnosticContext(mappedContext, ThreadContext.getImmutableContext()) {

    /**
     * Creates a new [MutableDiagnosticContext] populated with the current [ThreadContext].
     *
     * If not intending to modify the [ThreadContext], consider using [immutableDiagnosticContext] instead.
     * [immutableDiagnosticContext] is preferred in this case as it performs fewer unnecessary allocations.
     */
    public constructor() : this(ThreadContext.getContext())

    /**
     * Adds an entry to the Log4J context map.
     *
     * The entry will remain as part of the diagnostic context for the duration of the current coroutine context.
     *
     * This is the coroutine-compatible equivalent of [ThreadContext.put].
     *
     * @param key Key of the entry to add to the diagnostic context.
     * @param value Value of the entry to add to the diagnostic context.
     * @return This instance.
     */
    public fun put(key: String, value: String?): MutableDiagnosticContext {
        mappedContext[key] = value
        return this
    }

    /**
     * Adds all entries to the Log4J context map.
     *
     * The entries will remain as part of the diagnostic context for the duration of the current coroutine context.
     *
     * This is the coroutine-compatible equivalent of [ThreadContext.putAll].
     *
     * @param from Entries to add to the diagnostic context.
     * @return This instance.
     */
    public fun putAll(from: Map<String, String?>): MutableDiagnosticContext {
        mappedContext.putAll(from)
        return this
    }
}

/**
 * Enables the use of Log4J 2's [ThreadContext] with coroutines.
 *
 * # Example
 * The following example demonstrates usage of this class. All `assert`s pass. Note that only the mapped diagnostic
 * context is supported.
 *
 * ```kotlin
 * ThreadContext.put("kotlin", "rocks") // Put a value into the ThreadContext.
 * launch(immutableDiagnosticContext()) { // The contents of the ThreadContext are captured into the newly created CoroutineContext.
 *   assert(ThreadContext.get("kotlin") == "rocks")
 *
 *   withContext(MutableDiagnosticContext().put("kotlin", "is great") {
 *     assert(ThreadContext.get("kotlin") == "is great")
 *
 *     launch(Dispatchers.IO) {
 *       assert(ThreadContext.get("kotlin") == "is great") // The diagnostic context is inherited by child CoroutineContexts.
 *     }
 *   }
 *   assert(ThreadContext.get("kotlin") == "rocks") // The ThreadContext is reset when the CoroutineContext exits.
 * }
 * ```
 *
 * ## Combine with others
 * You may wish to combine this [ThreadContextElement] with other [CoroutineContext]s.
 *
 * ```kotlin
 * launch(Dispatchers.IO + immutableDiagnosticContext()) { ... }
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
 * withContext(MutableDiagnosticContext().put("kotlin", "is awesome") {
 *   assert(ThreadContext.get("kotlin") == "is awesome")
 * }
 * assert(ThreadContext.get("kotlin") == "rocks")
 * ```
 *
 * @param mappedContextBefore Mapped diagnostic context to apply for the duration of the corresponding [CoroutineContext].
 * @param mappedContextAfter Mapped diagnostic context to restore when the corresponding [CoroutineContext] exits.
 */
public open class DiagnosticContext internal constructor(
    private val mappedContextBefore: Map<String, String?>,
    private val mappedContextAfter: Map<String, String?> = mappedContextBefore
) : ThreadContextElement<DiagnosticContext>, AbstractCoroutineContextElement(Key) {

    /**
     * Key of [DiagnosticContext] in [CoroutineContext].
     */
    public companion object Key : CoroutineContext.Key<DiagnosticContext>

    /** @suppress */
    final override fun updateThreadContext(context: CoroutineContext): DiagnosticContext {
        setCurrent(mappedContextBefore)
        return this
    }

    /** @suppress */
    final override fun restoreThreadContext(context: CoroutineContext, oldState: DiagnosticContext) {
        setCurrent(oldState.mappedContextAfter)
    }

    private fun setCurrent(map: Map<String, String?>) {
        /*
         * The logic here varies significantly from how CloseableThreadContext works. CloseableThreadContext has the
         * luxury of assuming that it is appending new state to the existing state of the current thread. We cannot make
         * this assumption. It is very realistic for us to be restoring a context to a thread that has loads of state
         * that we are not at all interested in, due to the Log4J ThreadContext being implemented as a ThreadLocal.
         *
         * So, to make sure that the ThreadLocal belonging to the Thread servicing this CoroutineContext is has the
         * correct state, we first clear everything existing, and then apply the desired state.
         */
        ThreadContext.clearMap()
        ThreadContext.putAll(map)
    }
}