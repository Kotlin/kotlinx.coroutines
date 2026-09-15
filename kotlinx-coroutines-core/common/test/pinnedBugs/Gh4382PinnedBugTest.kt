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
        val perpetuallyBusyDispatcher = object : CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                // Never actually runs
            }
        }
        assertCoroutineHangs {
            coroutineScope {
                // Hangs and cannot be cancelled
                launch(perpetuallyBusyDispatcher) {
                    error("Unreachable code")
                }
                cancel()
            }
        }
    }
}
