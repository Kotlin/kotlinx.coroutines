package kotlinx.coroutines.pinnedBugs

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.BufferOverflow
import kotlinx.coroutines.flow.*
import kotlin.test.*

/**
 * PINNED BUG. Related issue: https://github.com/Kotlin/kotlinx.coroutines/issues/4383
 *
 * Pins the current behavior that surfaced in the specific issue.
 * CoroutineStart.UNDISPATCHED + collectLatest does not subscribe when expected
 * and can miss the initial emit
 */
class Gh4383PinnedBugTest : TestBase() {

    @Test
    fun testUndispatchedCollectLatestMissesValueEmittedBeforeItsInternalProducerRuns() = runTest {
        val flow = MutableSharedFlow<Int>(extraBufferCapacity = 1, onBufferOverflow = BufferOverflow.DROP_OLDEST)
        var valueReceived = false

        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            flow.collectLatest {
                valueReceived = true
            }
        }

        check(flow.tryEmit(1))

        yield()

        // Emitted value is never collected
        assertTrue(flow.subscriptionCount.value > 0)
        assertFalse(valueReceived)
        job.cancel()
    }

    // Simpler and broader(?) test from https://github.com/Kotlin/kotlinx.coroutines/pull/4488
    @Test
    fun testUndispatchedCollectLatestDoesNotSynchronouslySubscribeToUpstream() = runTest {
        expect(1)
        val myFlow = flow<Int> {
            expect(4) // 3
            yield()
            expect(5)
        }

        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            myFlow.collectLatest {
                expectUnreached()
            }
            finish(6)
        }

        expect(3) // 4
    }
}
