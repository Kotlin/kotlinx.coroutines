package kotlinx.coroutines.pinnedBugs

import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import kotlin.test.*
import kotlin.time.Duration.Companion.milliseconds

/**
 * PINNED BUG. Related issue: https://github.com/Kotlin/kotlinx.coroutines/issues/4685
 *
 * Pins the current behavior that surfaced in the specific issue.
 * runTest cancels but doesn't join backgroundScope, this may leave coroutines
 * running and produce UncaughtExceptionsBeforeTest on the next runTest.
 */
class Gh4685PinnedBugTest {

    @Test
    fun testBackgroundScopeJobIsNotJoinedBeforeRunTestReturns() = newSingleThreadContext("runTestThread-issue4685")
        .use { bgDispatcher ->
        lateinit var bgJob: Job

        // runTest is expected to join backgroundScope's job, but currently only cancels it and returns immediately
        runTest {
            bgJob = backgroundScope.launch(bgDispatcher) {
                withContext(NonCancellable) {
                    delay(100.milliseconds)
                    error("UncaughtException")
                }
            }
            delay(50.milliseconds)
        }

        assertTrue(bgJob.isCancelled)
        assertFalse(bgJob.isCompleted)

        val deadline = System.currentTimeMillis() + 10_000
        while (!bgJob.isCompleted) {
            if (System.currentTimeMillis() > deadline) fail("bgJob did not complete within timeout")
            Thread.sleep(10)
        }

        // Next runTest call throws UncaughtExceptionsBeforeTest because of the issue
        try {
            runTest {
                fail("unreached")
            }
            fail("expected UncaughtExceptionsBeforeTest to be thrown")
        } catch (e: UncaughtExceptionsBeforeTest) {
            val cause = assertIs<IllegalStateException>(e.suppressedExceptions.single())
            assertEquals("UncaughtException", cause.message)
        }
    }
}
