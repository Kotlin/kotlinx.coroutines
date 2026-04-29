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
 * You can derive a new [MDCContext] with additional entries via the `+` operators.
 *
 * ```
 * launch(MDCContext() + mapOf("key" to "value")) { // Propagate existing MDC with additional key-value pairs
 *     logger.info { "..." }                        // The MDC context contains the mapping here
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
 *     withContext(MDCContext() + mapOf("otherKey" to "otherValue")) { // This update will be captured as well
 *         delay(100)
 *         println(MDC.get("key")) // This will print "value"
 *         println(MDC.get("otherKey")) // This will print "otherValue"
 *     }
 * }
 * ```
 *
 * There is no way to implicitly propagate MDC context updates from inside the coroutine to the outer scope.
 * You have to capture the updated MDC context and restore it explicitly. For example:
 *
 * ```
 * val contextMap = withContext(MDCContext(mapOf("a" to "b"))) {
 *     withContext(MDCContext() + mapOf("key" to "value")) {
 *         withContext(MDCContext() + mapOf("key2" to "value2")) {
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

/**
 * Returns a new [MDCContext] with all entries from [map] added to this context.
 *
 * If [map] contains keys that are already present in this context, values from [map]
 * replace existing values.
 */
public operator fun MDCContext.plus(map: Map<String, String>): MDCContext = MDCContext((contextMap ?: emptyMap()) + map)

/**
 * Returns a new [MDCContext] with [pair] added to this context.
 *
 * [pair] is a key-value entry where `pair.first` is the key and `pair.second` is the value.
 * If the key `pair.first` is already present in this context, its existing value is replaced
 * with `pair.second`.
 */
public operator fun MDCContext.plus(pair: Pair<String, String>): MDCContext = MDCContext((contextMap ?: emptyMap()) + pair)

/**
 * Returns a new [MDCContext] with all [pairs] added to this context.
 *
 * For duplicate keys, later values from [pairs] replace earlier values and values already present
 * in this context.
 */
public operator fun MDCContext.plus(pairs: Iterable<Pair<String, String>>): MDCContext = MDCContext((contextMap ?: emptyMap()) + pairs)

/**
 * Returns a new [MDCContext] with all [pairs] from the sequence added to this context.
 *
 * For duplicate keys, later values from [pairs] replace earlier values and values already present
 * in this context.
 */
public operator fun MDCContext.plus(pairs: Sequence<Pair<String, String>>): MDCContext = MDCContext((contextMap ?: emptyMap()) + pairs)

/**
 * Returns a new [MDCContext] with all [pairs] from the array added to this context.
 *
 * For duplicate keys, later values from [pairs] replace earlier values and values already present
 * in this context.
 */
public operator fun MDCContext.plus(pairs: Array<Pair<String, String>>): MDCContext = MDCContext((contextMap ?: emptyMap()) + pairs)
