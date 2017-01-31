package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.AbstractCoroutineContextElement
import kotlin.coroutines.experimental.CoroutineContext

/**
 * User-specified name of coroutine. This name is used in debugging mode.
 * See [newCoroutineContext] for the description of coroutine debugging facilities.
 */
public data class CoroutineName(val name: String) : AbstractCoroutineContextElement(CoroutineName) {
    public companion object Key : CoroutineContext.Key<CoroutineName>
    override fun toString(): String = "CoroutineName($name)"
}
