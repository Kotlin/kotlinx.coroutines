package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import kotlin.test.*

class CancelledChannelLeakTest : TestBase() {
    /**
     * Tests that cancellation removes the elements from the channel's buffer.
     */
    @Test
    fun testBufferedChannelLeak() = runTest {
        for (capacity in listOf(Channel.CONFLATED, Channel.RENDEZVOUS, 1, 2, 5, 10)) {
            val channel = Channel<X>(capacity)
            val value = X()
            launch(start = CoroutineStart.UNDISPATCHED) {
                channel.send(value)
            }
            FieldWalker.assertReachableCount(1, channel) { it === value }
            channel.cancel()
            // the element must be removed so that there is no memory leak
            FieldWalker.assertReachableCount(0, channel) { it === value }
        }
    }

    class X
}