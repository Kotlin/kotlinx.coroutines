package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.time.Duration

internal actual object DefaultExecutor : CoroutineDispatcher(), Delay {

    private val delegate = WorkerDispatcher(name = "DefaultExecutor")

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        delegate.dispatch(context, block)
    }

    override fun scheduleResumeAfterDelay(timeout: Duration, continuation: CancellableContinuation<Unit>) {
        delegate.scheduleResumeAfterDelay(timeout, continuation)
    }

    override fun invokeOnTimeout(timeout: Duration, block: Runnable, context: CoroutineContext): DisposableHandle {
        return delegate.invokeOnTimeout(timeout, block, context)
    }

    actual fun enqueue(task: Runnable): Unit {
        delegate.dispatch(EmptyCoroutineContext, task)
    }
}

internal expect fun createDefaultDispatcher(): CoroutineDispatcher

@PublishedApi
internal actual val DefaultDelay: Delay = DefaultExecutor

public actual fun CoroutineScope.newCoroutineContext(context: CoroutineContext): CoroutineContext {
    val combined = coroutineContext + context
    return if (combined !== Dispatchers.Default && combined[ContinuationInterceptor] == null)
        combined + Dispatchers.Default else combined
}

public actual fun CoroutineContext.newCoroutineContext(addedContext: CoroutineContext): CoroutineContext {
    return this + addedContext
}

// No debugging facilities on native
internal actual inline fun <T> withCoroutineContext(context: CoroutineContext, countOrElement: Any?, block: () -> T): T = block()
internal actual inline fun <T> withContinuationContext(continuation: Continuation<*>, countOrElement: Any?, block: () -> T): T = block()
internal actual fun Continuation<*>.toDebugString(): String = toString()
internal actual val CoroutineContext.coroutineName: String? get() = null // not supported on native

internal actual class UndispatchedCoroutine<in T> actual constructor(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context, uCont) {
    override fun afterResume(state: Any?) = uCont.resumeWith(recoverResult(state, uCont))
}
