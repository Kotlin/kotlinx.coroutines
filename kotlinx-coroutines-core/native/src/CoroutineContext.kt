package kotlinx.coroutines

import kotlin.coroutines.*

internal actual object DefaultExecutor : CoroutineDispatcher(), Delay {

    private val delegate = WorkerDispatcher(name = "DefaultExecutor")

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        delegate.dispatch(context, block)
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        delegate.scheduleResumeAfterDelay(timeMillis, continuation)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        return delegate.invokeOnTimeout(timeMillis, block, context)
    }

    actual fun enqueue(task: Runnable): Unit {
        delegate.dispatch(EmptyCoroutineContext, task)
    }
}

internal expect fun createDefaultDispatcher(): CoroutineDispatcher

@PublishedApi
internal actual val DefaultDelay: Delay = DefaultExecutor

// No debugging facilities on native
internal actual fun Continuation<*>.toDebugString(): String = toString()
internal actual val CoroutineContext.coroutineName: String? get() = null // not supported on native
internal actual fun wrapContextWithDebug(context: CoroutineContext): CoroutineContext = context
