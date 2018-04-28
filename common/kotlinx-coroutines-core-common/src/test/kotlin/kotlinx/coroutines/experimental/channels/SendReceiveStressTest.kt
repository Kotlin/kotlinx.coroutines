package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class SendReceiveStressTest : TestBase() {

    // Emulate parametrized by hand :(

    @Test
    fun testArrayChannel() = runTest {
        testStress(ArrayChannel(2))
    }

    @Test
    fun testLinkedListChannel() = runTest {
        testStress(LinkedListChannel())
    }

    @Test
    fun testRendezvousChannel() = runTest {
        testStress(RendezvousChannel())
    }

    private suspend fun testStress(channel: Channel<Int>) {
        val n = 1_000 // Do not increase, otherwise node.js will fail with timeout :(
        val sender = launch(coroutineContext) {
            for (i in 1..n) {
                channel.send(i)
            }
            expect(2)
        }
        val receiver = launch(coroutineContext) {
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
