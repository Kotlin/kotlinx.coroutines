package kotlinx.coroutines

import kotlin.test.Test
import kotlin.test.assertTrue
import kotlinx.coroutines.runBlocking
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicReference

class DispatchFailureReproducerTest {
    @Test
    fun testDispatcherCloseDuringResume_reportsFailureAndCompletes() = runBlocking {
        val dispatcher = newSingleThreadContext("unreliable friend")

        // Capture exceptions reported to the coroutine exception handler
        val reported = AtomicReference<Throwable?>(null)
        val handler = CoroutineExceptionHandler { _, t -> reported.set(t) }

        val finallyRan = AtomicBoolean(false)

        // Use a CompletableDeferred instead of suspendCancellableCoroutine to avoid
        // depending on test-only APIs and to keep the scenario deterministic.
        val deferred = CompletableDeferred<Int>()

        val job = launch(dispatcher + handler, start = CoroutineStart.UNDISPATCHED) {
            try {
                // Await the deferred; it will be completed from another dispatcher
                deferred.await()
            } finally {
                // Mark that finally ran
                finallyRan.set(true)
            }
        }

        // Resume from another dispatcher after a short delay and close the dispatcher
        launch(Dispatchers.Default) {
            delay(50)
            dispatcher.close()
            deferred.complete(3)
        }

        // Wait for completion
        job.join()

        // The coroutine should have completed and its finally should have run
        assertTrue(finallyRan.get(), "finally block must run (no hang)")

        // Assert that a dispatch failure was reported (via CoroutineExceptionHandler)
        val reportedEx = reported.get()
        assertTrue(reportedEx != null, "Dispatch failure should be reported via CoroutineExceptionHandler")

        // Clean up
        dispatcher.close()
    }
}
