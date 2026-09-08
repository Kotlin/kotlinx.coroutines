package kotlinx.coroutines.pinnedBugs

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.coroutines.CoroutineContext
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
    fun testAtomicStartOnBrokenDispatcherHangsInsteadOfFailingFast() {
        val threadName = "gh4698-hung-thread"
        ignoreLostThreads(threadName) // The thread hangs and is impossible to terminate

        val completed = AtomicBoolean(false)
        val thread = Thread(null, {
            runTest {
                val job = launch(brokenDispatcher, start = CoroutineStart.ATOMIC) {}
                job.join()
            }
            completed.set(true)
        }, threadName)
        thread.isDaemon = true
        thread.start()

        // Wait for the thread to park
        val deadline = System.currentTimeMillis() + 1_000
        while (thread.isAlive && thread.state != Thread.State.WAITING && thread.state != Thread.State.TIMED_WAITING) {
            if (System.currentTimeMillis() > deadline) {
                fail("thread neither parked nor completed within 10s; state=${thread.state}")
            }
            Thread.yield()
        }

        assertTrue(thread.isAlive)
        assertFalse(completed.get())
    }
}
