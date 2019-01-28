package kotlinx.coroutines.android

import kotlinx.coroutines.*

@InternalCoroutinesApi
class DelayImpl : Delay {
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        continuation.cancel()
    }
}