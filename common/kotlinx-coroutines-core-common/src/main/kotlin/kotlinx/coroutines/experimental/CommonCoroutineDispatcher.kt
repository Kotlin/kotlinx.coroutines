package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*

public expect abstract class CoroutineDispatcher constructor() : AbstractCoroutineContextElement, ContinuationInterceptor {
    public open fun isDispatchNeeded(context: CoroutineContext): Boolean
    public abstract fun dispatch(context: CoroutineContext, block: Runnable)
    public override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T>
}

public expect interface Runnable {
    public fun run()
}

@Suppress("PropertyName")
public expect val DefaultDispatcher: CoroutineDispatcher
