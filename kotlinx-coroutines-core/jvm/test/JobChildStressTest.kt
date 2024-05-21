package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.test.*

/**
 * Testing the procedure of attaching a child to the parent job.
 */
class JobChildStressTest : TestBase() {
    private val N_ITERATIONS = 10_000 * stressTestMultiplier
    private val pool = newFixedThreadPoolContext(3, "JobChildStressTest")

    @AfterTest
    fun tearDown() {
        pool.close()
    }

    /**
     * Tests attaching a child while the parent is trying to finalize its state.
     *
     * Checks the following interleavings:
     * - A child attaches before the parent is cancelled.
     * - A child attaches after the parent is cancelled, but before the parent notifies anyone about it.
     * - A child attaches after the parent notifies the children about being cancelled,
     *   but before it starts waiting for its children.
     * - A child attempts to attach after the parent stops waiting for its children,
     *   which immediately cancels the child.
     */
    @Test
    @Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN")
    fun testChildAttachmentRacingWithCancellation() = runTest {
        val barrier = CyclicBarrier(3)
        repeat(N_ITERATIONS) {
            var wasLaunched = false
            var unhandledException: Throwable? = null
            val handler = CoroutineExceptionHandler { _, ex ->
                unhandledException = ex
            }
            val scope = CoroutineScope(pool + handler)
            val parent = createCompletableDeferredForTesting(it)
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

    /**
     * Tests attaching a child while the parent is waiting for the last child job to complete.
     *
     * Checks the following interleavings:
     * - A child attaches while the parent is already completing, but is waiting for its children.
     * - A child attempts to attach after the parent stops waiting for its children,
     *   which immediately cancels the child.
     */
    @Test
    fun testChildAttachmentRacingWithLastChildCompletion() {
        // All exceptions should get aggregated here
        repeat(N_ITERATIONS) {
            runBlocking {
                val rogueJob = AtomicReference<Job?>()
                /** not using [createCompletableDeferredForTesting] because we don't need extra children. */
                val deferred = CompletableDeferred<Unit>()
                // optionally, add a completion handler to the parent job, so that the child tries to enter a list with
                // multiple elements, not just one.
                if (it.mod(2) == 0) {
                    deferred.invokeOnCompletion { }
                }
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
