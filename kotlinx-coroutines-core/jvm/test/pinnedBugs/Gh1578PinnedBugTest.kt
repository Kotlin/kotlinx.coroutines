package kotlinx.coroutines.pinnedBugs

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.test.*
/**
 * PINNED BUG. Related issue: https://github.com/Kotlin/kotlinx.coroutines/issues/1578
 *
 * Pins the current behavior that surfaced in the specific issue.
 * runBlocking hangs if it has a child that never completes
 */
class Gh1578PinnedBugTest : TestBase() {

    @Test
    fun testRunBlockingHangsWithManualSupervisorJobChild() {
        val completed = AtomicBoolean(false)
        val thread = Thread {
            try {
                runBlocking {
                    val supervisorJob = SupervisorJob(coroutineContext[Job])
                    assertTrue(supervisorJob.isActive)
                    // supervisorJob is never completed/cancelled -- runBlocking cannot complete
                }
                completed.set(true)
            } catch (_: InterruptedException) { }
        }
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

        // Unblock the thread
        thread.interrupt()
        thread.join()
    }
}
