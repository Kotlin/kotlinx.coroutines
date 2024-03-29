package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class SendReceiveStressTest : TestBase() {

    // Emulate parametrized by hand :(

    @Test
    fun testBufferedChannel() = runTest {
        testStress(Channel(2))
    }

    @Test
    fun testUnlimitedChannel() = runTest {
        testStress(Channel(Channel.UNLIMITED))
    }

    @Test
    fun testRendezvousChannel() = runTest {
        testStress(Channel(Channel.RENDEZVOUS))
    }

    private suspend fun testStress(channel: Channel<Int>) = coroutineScope {
        val n = 100 // Do not increase, otherwise node.js will fail with timeout :(
        val sender = launch {
            for (i in 1..n) {
                channel.send(i)
            }
            expect(2)
        }
        val receiver = launch {
            for (i in 1..n) {
                val next = channel.receive()
                check(next == i)
            }
            expect(3)
        }
        expect(1)
        sender.join()
        receiver.join()
        finish(4)
    }
}
