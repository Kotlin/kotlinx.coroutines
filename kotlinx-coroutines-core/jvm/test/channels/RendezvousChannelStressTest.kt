package kotlinx.coroutines.channels

import kotlinx.coroutines.TestBase
import kotlinx.coroutines.flow.consumeAsFlow
import kotlinx.coroutines.flow.first
import org.junit.Test
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.concurrent.thread

class RendezvousChannelStressTest : TestBase() {

    @Test
    fun testOfferByThread_consumeAsFlow_StressTest() = runTest {
        val channel = Channel<Long>(Channel.RENDEZVOUS)
        val valueReceived = AtomicBoolean(false)
        try {
            thread {
                try {
                    var i = 0L
                    while (!valueReceived.get()) {
                        i++
                        channel.offer(i)
                    }
                } catch (e: ClosedSendChannelException) {

                }
            }

            channel.consumeAsFlow().first { true }
        } finally {
            valueReceived.set(true)
        }
    }


    @Test
    fun testOfferByThread_consumeAsChannel_StressTest() = runTest {
        val channel = Channel<Long>(Channel.RENDEZVOUS)
        val valueReceived = AtomicBoolean(false)
        try {
            thread {
                try {
                    var i = 0L
                    while (!valueReceived.get()) {
                        i++
                        channel.offer(i)
                    }
                } catch (e: ClosedSendChannelException){

                }
            }

            @Suppress("DEPRECATION")
            channel.first { true }
        } finally {
            valueReceived.set(true)
        }
    }
}
