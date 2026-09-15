package kotlinx.coroutines.pinnedBugs

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.test.*

/**
 * PINNED BUG. Related issue: https://github.com/Kotlin/kotlinx.coroutines/issues/1578
 *
 * Pins the current behavior that surfaced in the specific issue.
 * runBlocking/coroutineScope hangs if it has a child that never completes
 */
class Gh1578PinnedBugTest : TestBase() {

    @Test
    fun testRunBlockingHangsWithManualSupervisorJobChild() = runTest {
        assertCoroutineHangs {
            coroutineScope {
                val supervisorJob = SupervisorJob(coroutineContext[Job])
                assertTrue(supervisorJob.isActive)
                // supervisorJob is never completed/cancelled and coroutineScope cannot complete
            }
        }
    }
}
