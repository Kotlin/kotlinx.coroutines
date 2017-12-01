package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.CoroutineContext

public expect object Unconfined : CoroutineDispatcher {
    override fun isDispatchNeeded(context: CoroutineContext): Boolean
    override fun dispatch(context: CoroutineContext, block: Runnable)
}
