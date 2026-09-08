package kotlinx.coroutines.pinnedBugs

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.coroutines.CoroutineContext
import kotlin.test.*

/**
 * PINNED BUG. Related issue: https://github.com/Kotlin/kotlinx.coroutines/issues/4382
 *
 * Pins the current behavior that surfaced in the specific issue.
 * cancel() hangs the thread when a child is launched via a dispatcher whose
 * dispatch() never runs the submitted block
 */
class Gh4382PinnedBugTest : TestBase() {

    @Test
    fun testCancelHangsWhenChildIsLaunchedOnDispatcherThatNeverRunsIt() {
        val completed = AtomicBoolean(false)

        val threadName = "Gh4382PinnedBugTest-hung-thread"
        ignoreLostThreads(threadName) // The thread hangs and is impossible to terminate

        val thread = Thread(null, {
            runBlocking {
                val perpetuallyBusyDispatcher = object : CoroutineDispatcher() {
                    override fun dispatch(context: CoroutineContext, block: Runnable) {
                        // never actually runs
                    }
                }
                coroutineScope {
                    // Hangs the thread and cannot be cancelled
                    launch(perpetuallyBusyDispatcher) {
                        error("Unreachable code")
                    }
                    cancel()
                }
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
            Thread.sleep(100)
        }
        assertTrue(thread.isAlive)
        assertFalse(completed.get())
    }
}
