package kotlinx.coroutines.pinnedBugs

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/**
 * PINNED BUG. Related issue: https://github.com/Kotlin/kotlinx.coroutines/issues/2817
 *
 * Pins the current behavior that surfaced in the specific issue.
 * The issue contains two cases of the operator fusion unexpected behaviour:
 * The buffer(0) is not applied as expected when used in
 * sequence with produceIn and shareIn and produces different results.
 */
class Gh2817PinnedBugTest : TestBase() {

    @Test
    fun testSharedFlowBufferZeroProduceInIsDiscarded() = runTest {
        val stream = MutableSharedFlow<Unit>()
        val channel = stream
            .buffer(0) // buffer(0) applied before produceIn is discarded, default capacity (64) is used
            .produceIn(this)
        yield()
        var emitted = 0
        // To fail faster if the behaviour changes
        withTimeout(10.seconds) {
            repeat(PRODUCEIN_DEFAULT_BUFFERED) {
                stream.emit(Unit)
                emitted++
            }
        }
        assertEquals(PRODUCEIN_DEFAULT_BUFFERED, emitted)
        // The next emit suspends until it will be collected
        val probe = launch {
            stream.emit(Unit)
            fail("unreachable code")
        }
        yield()
        assertTrue(probe.isActive)
        probe.cancel()
        channel.cancel()
        coroutineContext.cancelChildren()
    }

    @Test
    fun testChannelFlowShareInBufferZeroAppliesOnlyUpstream() = runTest {
        var sent = 0
        val shared = channelFlow {
            while (true) {
                send(Unit)
                sent++
            }
        }
            .buffer(capacity = 0) // buffer is only applied upstream, the default buffer is used downstream
            .shareIn(this, SharingStarted.WhileSubscribed(), replay = 0)
        val downstream = launch { shared.collect { awaitCancellation() } }
        repeat(SHAREIN_SETTLE_YIELDS) { yield() }
        assertEquals(SHAREIN_DEFAULT_BUFFERED, sent)
        downstream.cancel()
        coroutineContext.cancelChildren()
    }

    companion object {
        private const val PRODUCEIN_DEFAULT_BUFFERED = 65
        private const val SHAREIN_DEFAULT_BUFFERED = 66
        private const val SHAREIN_SETTLE_YIELDS = 70
    }
}
