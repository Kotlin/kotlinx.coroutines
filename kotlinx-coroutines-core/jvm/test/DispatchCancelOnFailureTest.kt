package kotlinx.coroutines

import kotlin.test.Test
import kotlin.test.assertTrue
import kotlin.coroutines.CoroutineContext
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicReference

class DispatchCancelOnFailureTest {
    @Test
    fun testCancelJobOnDispatchFailure() = runBlocking {
        val dispatcher = object : CoroutineDispatcher() {
            override fun isDispatchNeeded(context: CoroutineContext): Boolean = true
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                throw RuntimeException("dispatch failure")
            }
        }

        val reported = AtomicReference<Throwable?>(null)
        val handler = CoroutineExceptionHandler { _, t -> reported.set(t) }

    val job = Job()
        val finallyRan = AtomicBoolean(false)
        val deferred = CompletableDeferred<Int>()

        val coro = launch(job + dispatcher + handler, start = CoroutineStart.UNDISPATCHED) {
            try {
                deferred.await()
            } finally {
                finallyRan.set(true)
            }
        }

        // resume from another dispatcher; this will cause dispatch to throw and safeDispatch
        // should cancel the coroutine's Job and report the original exception
        launch(Dispatchers.Default) {
            delay(50)
            deferred.complete(3)
        }

    coro.join()

    // The coroutine that was launched (`coro`) should be cancelled when dispatch fails.
    // Checking `coro.isCancelled` is more reliable than checking the parent `job` instance,
    // because `launch` may create a child Job in the coroutine context.
    assertTrue(coro.isCancelled, "coroutine should be cancelled on dispatch failure")
        assertTrue(finallyRan.get(), "finally block must run")
        assertTrue(reported.get() != null, "Dispatch failure should be reported via CoroutineExceptionHandler")
    }
}
