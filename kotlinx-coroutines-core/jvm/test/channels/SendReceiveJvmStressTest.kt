package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.runner.*
import org.junit.runners.*
import kotlin.test.*

@RunWith(Parameterized::class)
class SendReceiveJvmStressTest(private val channel: Channel<Int>) : TestBase() {

    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = listOf(
            Channel<Int>(1),
            Channel (10),
            Channel(1_000_000),
            Channel(Channel.UNLIMITED),
            Channel(Channel.RENDEZVOUS)
        ).map { arrayOf<Any>(it) }
    }

    @Test
    fun testStress() = runTest {
        val n = 100_000 * stressTestMultiplier
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
