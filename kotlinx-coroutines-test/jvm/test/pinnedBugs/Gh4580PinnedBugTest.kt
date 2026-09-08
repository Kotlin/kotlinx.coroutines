package kotlinx.coroutines.pinnedBugs

import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import kotlin.test.*

/**
 * PINNED BUG. Related issue: https://github.com/Kotlin/kotlinx.coroutines/issues/4580
 *
 * Pins the current behavior that surfaced in the specific issue.
 * When only a dispatcher is passed, a new task may arrive there by the time runTest is
 * no longer processing the tasks in the test scheduler. The cleanup never runs
 */
class Gh4580PinnedBugTest {

    @Test
    fun testTaskLaunchedOnBareDispatcherIsOrphanedByRunTest() {
        val dispatcher = StandardTestDispatcher()
        val resource = CompletableDeferred<Unit>()
        var cleanedUp = false
        lateinit var orphanedJob: Job

        TestScope(dispatcher).runTest {
            orphanedJob = GlobalScope.launch(dispatcher) {
                try {
                    resource.await()
                } finally {
                    cleanedUp = true
                }
            }
        }

        assertTrue(orphanedJob.isActive)
        assertFalse(orphanedJob.isCancelled)
        assertFalse(orphanedJob.isCompleted)
        assertFalse(cleanedUp)

        resource.complete(Unit)
        assertFalse(orphanedJob.isCompleted)
        assertFalse(cleanedUp)

        dispatcher.scheduler.advanceUntilIdle()
        assertTrue(orphanedJob.isCompleted)
        assertTrue(cleanedUp)
    }
}
