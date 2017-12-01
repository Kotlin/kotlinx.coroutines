package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.CoroutineContext

public expect abstract class CoroutineDispatcher : ContinuationInterceptor {
    public open fun isDispatchNeeded(context: CoroutineContext): Boolean
    public abstract fun dispatch(context: CoroutineContext, block: Runnable)
}

public expect interface Runnable {
    public fun run()
}

@Suppress("PropertyName")
public expect val DefaultDispatcher: CoroutineDispatcher
