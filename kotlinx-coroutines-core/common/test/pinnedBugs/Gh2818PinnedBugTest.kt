package kotlinx.coroutines.pinnedBugs

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.*
import kotlin.test.*
import kotlin.time.Duration.Companion.milliseconds

/**
 * PINNED BUG. Related issue: https://github.com/Kotlin/kotlinx.coroutines/issues/2818
 *
 * Pins the current behavior that surfaced in the specific issue.
 * The RENDEZVOUS buffer allows the first emit to bypass the backpressure limitation
 */
class Gh2818PinnedBugTest : TestBase() {

    @Test
    fun testSharedFlowBufferRendezvousProduceInLetsOneEmitBypassBackpressure() = runTest {
        expect(1)
        val stream = MutableSharedFlow<Unit>()
        val channel = stream.onEach { }.buffer(Channel.RENDEZVOUS).produceIn(this)
        yield()
        expect(2)
        withTimeout(1000.milliseconds) {
            stream.emit(Unit) // Expected to suspend on first emit
        }
        expect(3)
        val job = launch {
            expect(5)
            stream.emit(Unit) // Only the second emit suspends until the value is collected
            expectUnreached()
        }
        expect(4)
        yield()
        expect(6)
        assertTrue(job.isActive)
        job.cancel()
        channel.cancel()
        finish(7)
    }
}
