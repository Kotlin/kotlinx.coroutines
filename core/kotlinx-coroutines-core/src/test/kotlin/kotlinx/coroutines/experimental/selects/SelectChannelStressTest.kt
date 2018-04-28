package kotlinx.coroutines.experimental.selects

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.intrinsics.*
import kotlin.test.*

class SelectChannelStressTest: TestBase() {

    @Test
    fun testSelectSendResourceCleanupArrayChannel() = runTest {
        val channel = ArrayChannel<Int>(1)
        val n = 10_000_000 * stressTestMultiplier
        expect(1)
        channel.send(-1) // fill the buffer, so all subsequent sends cannot proceed
        repeat(n) { i ->
            select {
                channel.onSend(i) { expectUnreached() }
                default { expect(i + 2) }
            }
        }
        finish(n + 2)
    }

    @Test
    fun testSelectReceiveResourceCleanupArrayChannel() = runTest {
        val channel = ArrayChannel<Int>(1)
        val n = 10_000_000 * stressTestMultiplier
        expect(1)
        repeat(n) { i ->
            select {
                channel.onReceive { expectUnreached() }
                default { expect(i + 2) }
            }
        }
        finish(n + 2)
    }

    @Test
    fun testSelectSendResourceCleanupRendezvousChannel() = runTest {
        val channel = RendezvousChannel<Int>()
        val n = 1_000_000 * stressTestMultiplier
        expect(1)
        repeat(n) { i ->
            select {
                channel.onSend(i) { expectUnreached() }
                default { expect(i + 2) }
            }
        }
        finish(n + 2)
    }

    @Test
    fun testSelectReceiveResourceRendezvousChannel() = runTest {
        val channel = RendezvousChannel<Int>()
        val n = 1_000_000 * stressTestMultiplier
        expect(1)
        repeat(n) { i ->
            select {
                channel.onReceive { expectUnreached() }
                default { expect(i + 2) }
            }
        }
        finish(n + 2)
    }

    internal fun <R> SelectBuilder<R>.default(block: suspend () -> R) {
        this as SelectBuilderImpl // type assertion
        if (!trySelect(null)) return
        block.startCoroutineUndispatched(this)
    }
}
