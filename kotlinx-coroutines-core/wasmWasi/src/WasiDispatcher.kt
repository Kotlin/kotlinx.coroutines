package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

internal object WasiDispatcher: CoroutineDispatcher(), Delay {
    override fun limitedParallelism(parallelism: Int): CoroutineDispatcher {
        parallelism.checkParallelism()
        return this
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        registerEvent(0) { block.run() }
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        registerEvent(delayToNanos(timeMillis)) { block.run() }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val event = registerEvent(delayToNanos(timeMillis)) {
            with(continuation) { resumeUndispatched(Unit) }
        }
        continuation.disposeOnCancellation(event)
    }
}