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
 * or
 *
 * ```
 * launch(MDCContext("kotlin" to "rocks")) {
 *     logger.info { "..." }   // The MDC context contains the mapping here
 * }
 * ```
 *
 * Note that you cannot update MDC context from inside the coroutine simply
 * using [MDC.put]. These updates are going to be lost on the next suspension and
 * reinstalled to the MDC context that was captured or explicitly specified in
 * [contextMap] when this object was created on the next resumption.
 *
 * For example, the following code will not work as expected:
 *
 * ```
 * launch(MDCContext()) {
 *     MDC.put("key", "value") // This update will be lost
 *     delay(100)
 *     println(MDC.get("key")) // This will print null
 * }
 * ```
 *
 * Instead, you should use [withContext] to capture the updated MDC context:
 *
 * ```
 * launch(MDCContext()) {
 *     MDC.put("key", "value") // This update will be captured
 *     withContext(MDCContext()) {
 *         delay(100)
 *         println(MDC.get("key")) // This will print "value"
 *     }
 * }
 * ```
 *
 * There is no way to implicitly propagate MDC context updates from inside the coroutine to the outer scope.
 * You have to capture the updated MDC context and restore it explicitly. For example:
 *
 * ```
 * MDC.put("a", "b")
 * val contextMap = withContext(MDCContext()) {
 *     MDC.put("key", "value")
 *     withContext(MDCContext()) {
 *         MDC.put("key2", "value2")
 *         withContext(MDCContext()) {
 *             yield()
 *             MDC.getCopyOfContextMap()
 *         }
 *     }
 * }
 * // contextMap contains: {"a"="b", "key"="value", "key2"="value2"}
 * MDC.setContextMap(contextMap)
 * ```
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

    /**
     * Alternative constructor to put [key-value-pairs][keyValuePairs] into the [MDC].
     *
     * Example:
     * ```
     * withContext(MDCContext("kotlin" to "rocks")) {
     *     // The MDC context contains the mapping here
     * }
     * ```
     *
     * Note: The old MDC values will be restored when the coroutine context is restored.
     * ```kotlin
     * MDC.put("kotlin", "is great")
     * withContext(MDCContext("kotlin" to "rocks")) {
     *     println(MDC.get("kotlin")) // prints "rocks"
     * }
     * println(MDC.get("kotlin")) // prints "is great"
     * ```
     *
     * @param keyValuePairs key-value-pairs with will be put into the MDC
     */
    public constructor(vararg keyValuePairs: Pair<String, String>): this(
        (MDC.getCopyOfContextMap() ?: emptyMap()) + keyValuePairs,
    )

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
