package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

class JobActivationStressTest : TestBase() {
    private val N_ITERATIONS = 10_000 * stressTestMultiplier

    /**
     * Perform concurrent start and cancel of a job with prior installed completion handlers
     */
    @Test
    @Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN")
    fun testActivation() = runTest {
        val barrier = ConcurrentCyclicBarrier(3)
        newFixedThreadPoolContext(3, "JobActivationStressTest").use { pool ->
            repeat(N_ITERATIONS) {
                var wasStarted = false
                val d = async(pool + NonCancellable, start = CoroutineStart.LAZY) {
                    wasStarted = true
                    throw TestException()
                }
                // need to add on completion handler
                val causeHolder = CompletableDeferred<Throwable?>()
                // we await on causeHolder below to work around the fact that completion listeners
                // are invoked after the job is in the final state, so when "d.join()" completes there is
                // no guarantee that this listener was already invoked
                d.invokeOnCompletion {
                    causeHolder.complete(it)
                }
                // concurrent cancel
                val canceller = launch(pool) {
                    barrier.await()
                    d.cancel()
                }
                // concurrent start
                val starter = launch(pool) {
                    barrier.await()
                    d.start()
                }
                barrier.await()
                joinAll(d, canceller, starter)
                if (wasStarted) {
                    val exception = d.getCompletionExceptionOrNull()
                    assertIs<TestException>(exception, "exception=$exception")
                    val cause = causeHolder.await()
                    assertIs<TestException>(cause, "cause=$cause")
                }
            }
        }
    }
}
