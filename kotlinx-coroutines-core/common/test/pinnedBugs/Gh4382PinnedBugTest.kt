package kotlinx.coroutines.pinnedBugs

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.test.*

/**
 * PINNED BUG. Related issue: https://github.com/Kotlin/kotlinx.coroutines/issues/4382
 *
 * Pins the current behavior that surfaced in the specific issue.
 * cancel() hangs the coroutine when a child is launched via a dispatcher whose
 * dispatch() never runs the submitted block
 */
class Gh4382PinnedBugTest : TestBase() {

    @Test
    fun testCancelHangsWhenChildIsLaunchedOnDispatcherThatNeverRunsIt() = runTest {
        spinAwaitingCompletion {
            val perpetuallyBusyDispatcher = object : CoroutineDispatcher() {
                override fun dispatch(context: CoroutineContext, block: Runnable) {
                    // Never actually runs
                }
            }
            coroutineScope {
                // Hangs and cannot be cancelled
                launch(perpetuallyBusyDispatcher) {
                    error("Unreachable code")
                }
                cancel()
            }
        }
    }

    // Asserts that the coroutine cannot progress
    private suspend fun <T> spinAwaitingCompletion(attempts: Int = 100, hangingTest: suspend () -> T) {
        val dispatcher = currentCoroutineContext()[ContinuationInterceptor]!!
        val deferred = GlobalScope.async(dispatcher) {
            hangingTest()
        }
        repeat(attempts) {
            yield()
            if (deferred.isCompleted) {
                fail("Expected a hanging test, got ${deferred.await()}")
            }
        }
    }
}
