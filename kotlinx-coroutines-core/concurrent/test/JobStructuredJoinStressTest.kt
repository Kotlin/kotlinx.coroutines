package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*

/**
 * Test a race between job failure and join.
 *
 * See [#1123](https://github.com/Kotlin/kotlinx.coroutines/issues/1123).
 */
class JobStructuredJoinStressTest : TestBase() {
    private val nRepeats = 10_000 * stressTestMultiplier

    @Test
    fun testStressRegularJoin() = runTest {
        stress(Job::join)
    }

    @Test
    fun testStressSuspendCancellable() = runTest {
        stress { job ->
            suspendCancellableCoroutine { cont ->
                job.invokeOnCompletion { cont.resume(Unit) }
            }
        }
    }

    @Test
    fun testStressSuspendCancellableReusable() = runTest {
        stress { job ->
            suspendCancellableCoroutineReusable { cont ->
                job.invokeOnCompletion { cont.resume(Unit) }
            }
        }
    }

    private fun stress(join: suspend (Job) -> Unit) {
        expect(1)
        repeat(nRepeats) { index ->
            assertFailsWith<TestException> {
                runBlocking {
                    // launch in background
                    val job = launch(Dispatchers.Default) {
                        throw TestException("OK") // crash
                    }
                    try {
                        join(job)
                        error("Should not complete successfully")
                    } catch (e: CancellationException) {
                        // must always crash with cancellation exception
                        expect(2 + index)
                    } catch (e: Throwable) {
                        error("Unexpected exception", e)
                    }
                }
            }
        }
        finish(2 + nRepeats)
    }
}
