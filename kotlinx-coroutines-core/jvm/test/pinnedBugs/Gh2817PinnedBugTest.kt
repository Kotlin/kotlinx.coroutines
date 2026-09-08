package kotlinx.coroutines.pinnedBugs

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

/**
 * PINNED BUG. Related issue: https://github.com/Kotlin/kotlinx.coroutines/issues/2817
 *
 * Pins the current behavior that surfaced in the specific issue.
 * There are two distinct fusion bugs so there are two tests here:
 * The buffer(0) is not applied as expected when used in
 * sequence with produceIn and shareIn
 */
class Gh2817PinnedBugTest : TestBase() {

    @Test
    fun testSharedFlowBufferZeroProduceInDoesNotApplyRendezvousBackpressure() = runTest {
        val stream = MutableSharedFlow<Unit>()
        val channel = stream
            .buffer(0) // buffer(0) before produceIn is discarded, default capacity (64) is used
            .produceIn(this)
        yield()

        var emitted = 0
        repeat(PRODUCEIN_DEFAULT_BUFFERED) {
            stream.emit(Unit)
            emitted++
        }
        assertEquals(PRODUCEIN_DEFAULT_BUFFERED, emitted)

        // The next emit suspends until it will be collected
        val probe = launch {
            stream.emit(Unit)
            expectUnreached()
        }
        yield()
        assertTrue(probe.isActive)

        probe.cancel()
        channel.cancel()
        coroutineContext.cancelChildren()
    }

    @Test
    fun testChannelFlowBufferZeroShareInAppliesBufferOnlyUpstream() = runTest {
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
        private const val PRODUCEIN_DEFAULT_BUFFERED = 65 // BUFFER(64) + RENDEZVOUS issue 2818

        private const val SHAREIN_DEFAULT_BUFFERED = 66 // BUFFER(64) + single collect on subscribe + RENDEZVOUS
        private const val SHAREIN_SETTLE_YIELDS = 70
    }
}
