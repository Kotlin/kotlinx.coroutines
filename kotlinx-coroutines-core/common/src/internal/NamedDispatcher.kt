package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.DefaultDelay
import kotlin.coroutines.*

/**
 * Wrapping dispatcher that has a nice user-supplied `toString()` representation
 */
internal class NamedDispatcher(
    private val dispatcher: CoroutineDispatcher,
    private val name: String
) : CoroutineDispatcher(), Delay by (dispatcher as? Delay ?: DefaultDelay) {

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = dispatcher.isDispatchNeeded(context)

    override fun dispatch(context: CoroutineContext, block: Runnable) = dispatcher.dispatch(context, block)

    @InternalCoroutinesApi
    override fun dispatchYield(context: CoroutineContext, block: Runnable) = dispatcher.dispatchYield(context, block)

    override fun toString(): String {
        return name
    }
}