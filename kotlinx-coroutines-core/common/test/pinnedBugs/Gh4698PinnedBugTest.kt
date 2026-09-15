package kotlinx.coroutines.pinnedBugs

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.test.*

/**
 * PINNED BUG. Related issue: https://github.com/Kotlin/kotlinx.coroutines/issues/4698
 *
 * Pins the current behavior that surfaced in the specific issue.
 * If a dispatcher throws an exception when dispatching a coroutine using
 * CoroutineStart.ATOMIC it will silently hang without any errors or diagnostics
 */
class Gh4698PinnedBugTest : TestBase() {

    private val brokenDispatcher = object : CoroutineDispatcher() {
        override fun dispatch(context: CoroutineContext, block: Runnable) = TODO("dispatcher is broken")
    }

    @Test
    fun testAtomicStartOnBrokenDispatcherHangsInsteadOfFailingFast() = runTest {
        assertCoroutineHangs {
            coroutineScope {
                val job = launch(brokenDispatcher, start = CoroutineStart.ATOMIC) {}
                job.join()
            }
        }
    }
}
