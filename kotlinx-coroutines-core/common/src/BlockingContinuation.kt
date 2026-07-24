package kotlinx.coroutines

/**
 * Experimental bridge for implementations that keep a suspending call on its current thread.
 *
 * This deliberately bypasses continuation dispatch: the caller waits in [await] and the thread
 * completing the continuation invokes [signal].
 */
internal interface BlockingContinuationSupport {
    fun createBlockingWaiter(): BlockingContinuationWaiter
}

internal interface BlockingContinuationWaiter {
    fun await()
    fun signal()
}
