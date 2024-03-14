package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.test.*

class JobChildStressTest : TestBase() {
    private val N_ITERATIONS = 10_000 * stressTestMultiplier
    private val pool = newFixedThreadPoolContext(3, "JobChildStressTest")

    @After
    fun tearDown() {
        pool.close()
    }

    /**
     * Perform concurrent launch of a child job & cancellation of the explicit parent job
     */
    @Test
    @Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN")
    fun testChild() = runTest {
        val barrier = CyclicBarrier(3)
        repeat(N_ITERATIONS) {
            var wasLaunched = false
            var unhandledException: Throwable? = null
            val handler = CoroutineExceptionHandler { _, ex ->
                unhandledException = ex
            }
            val scope = CoroutineScope(pool + handler)
            val parent = CompletableDeferred<Unit>()
            // concurrent child launcher
            val launcher = scope.launch {
                barrier.await()
                // A: launch child for a parent job
                launch(parent) {
                    wasLaunched = true
                    throw TestException()
                }
            }
            // concurrent cancel
            val canceller = scope.launch {
                barrier.await()
                // B: cancel parent job of a child
                parent.cancel()
            }
            barrier.await()
            joinAll(launcher, canceller, parent)
            assertNull(unhandledException)
            if (wasLaunched) {
                val exception = parent.getCompletionExceptionOrNull()
                assertIs<TestException>(exception, "exception=$exception")
            }
        }
    }

    @Test
    fun testFailingChildIsAddedWhenJobFinalizesItsState() {
        // All exceptions should get aggregated here
        repeat(N_ITERATIONS) {
            runBlocking {
                val rogueJob = AtomicReference<Job?>()
                val deferred = CompletableDeferred<Unit>()
                launch(pool + deferred) {
                    deferred.complete(Unit) // Transition deferred into "completing" state waiting for current child
                    // **Asynchronously** submit task that launches a child so it races with completion
                    pool.executor.execute {
                        rogueJob.set(launch(pool + deferred) {
                            throw TestException("isCancelled: ${coroutineContext.job.isCancelled}")
                        })
                    }
                }

                deferred.join()
                val rogue = rogueJob.get()
                if (rogue?.isActive == true) {
                    throw TestException("Rogue job $rogue with parent " + rogue.parent + " and children list: " + rogue.parent?.children?.toList())
                }
            }
        }
    }
}
