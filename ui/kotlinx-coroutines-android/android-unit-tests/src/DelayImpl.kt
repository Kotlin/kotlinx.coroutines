package kotlinx.coroutines.android

import kotlinx.coroutines.*

// Class for testing service loader
class DelayImpl : Delay {
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        continuation.cancel()
    }
}
