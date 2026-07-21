package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import kotlin.test.*


class BufferedChannelStressTest1 : BufferedChannelStressTest(1)
class BufferedChannelStressTest10 : BufferedChannelStressTest(10)
class BufferedChannelStressTest100 : BufferedChannelStressTest(100)
class BufferedChannelStressTest100000 : BufferedChannelStressTest(100_000)
class BufferedChannelStressTest1000000 : BufferedChannelStressTest(1_000_000)

abstract class BufferedChannelStressTest(private val capacity: Int) : TestBase() {
    @Test
    fun testStress() = runTest {
        val n = 100_000 * stressTestMultiplier
        val q = Channel<Int>(capacity)
        val sender = launch {
            for (i in 1..n) {
                q.send(i)
            }
            expect(2)
        }
        val receiver = launch {
            for (i in 1..n) {
                val next = q.receive()
                check(next == i)
            }
            expect(3)
        }
        expect(1)
        sender.join()
        receiver.join()
        finish(4)
    }

    @Test
    fun testBurst() = runTest {
        if (capacity >= 100_000) return@runTest
        repeat(10_000 * stressTestMultiplier) {
            val channel = Channel<Int>(capacity)
            val sender = launch(Dispatchers.Default) {
                for (i in 1..capacity * 2) {
                    channel.send(i)
                }
            }
            val receiver = launch(Dispatchers.Default) {
                for (i in 1..capacity * 2) {
                    val next = channel.receive()
                    check(next == i)
                }
            }
            sender.join()
            receiver.join()
        }
    }
}
