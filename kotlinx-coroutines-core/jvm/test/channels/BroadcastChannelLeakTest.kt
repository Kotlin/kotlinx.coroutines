package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class BroadcastChannelLeakTest : TestBase() {
    @Test
    fun testBufferedBroadcastChannelSubscriptionLeak() {
        checkLeak { BroadcastChannelImpl(1) }
    }

    @Test
    fun testConflatedBroadcastChannelSubscriptionLeak() {
        checkLeak { ConflatedBroadcastChannel() }
    }

    enum class TestKind { BROADCAST_CLOSE, SUB_CANCEL, BOTH }

    private fun checkLeak(factory: () -> BroadcastChannel<String>) = runTest {
        for (kind in TestKind.values()) {
            val broadcast = factory()
            val sub = broadcast.openSubscription()
            broadcast.send("OK")
            assertEquals("OK", sub.receive())
            // now close broadcast
            if (kind != TestKind.SUB_CANCEL) broadcast.close()
            // and then cancel subscription
            if (kind != TestKind.BROADCAST_CLOSE) sub.cancel()
            // subscription should not be reachable from the channel anymore
            FieldWalker.assertReachableCount(0, broadcast) { it === sub }
        }
    }
}