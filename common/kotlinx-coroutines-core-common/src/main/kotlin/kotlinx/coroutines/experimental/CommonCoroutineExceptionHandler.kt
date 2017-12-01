package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.CoroutineContext

public expect fun handleCoroutineException(context: CoroutineContext, exception: Throwable)

public expect interface CoroutineExceptionHandler : CoroutineContext.Element {
    public companion object Key : CoroutineContext.Key<CoroutineExceptionHandler>
    public fun handleException(context: CoroutineContext, exception: Throwable)
}

@Suppress("FunctionName")
public expect fun CoroutineExceptionHandler(handler: (CoroutineContext, Throwable) -> Unit): CoroutineExceptionHandler
