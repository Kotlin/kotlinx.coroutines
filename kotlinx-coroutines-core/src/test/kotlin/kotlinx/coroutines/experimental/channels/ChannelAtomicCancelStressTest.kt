package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.util.*
import org.junit.Assert.*

@RunWith(Parameterized::class)
class ChannelAtomicCancelStressTest(val kind: TestChannelKind) {
    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = TestChannelKind.values().map { arrayOf<Any>(it) }
    }

    val TEST_DURATION = 3000L

    val channel = kind.create()
    val senderDone = RendezvousChannel<Boolean>()
    val receiverDone = RendezvousChannel<Boolean>()

    var lastSent = 0
    var lastReceived = 0

    var stoppedSender = 0
    var stoppedReceiver = 0

    var missedCnt = 0
    var dupCnt = 0

    lateinit var sender: Job
    lateinit var receiver: Job

    @Test
    fun testAtomicCancelStress() = runBlocking {
        val deadline = System.currentTimeMillis() + TEST_DURATION
        launchSender()
        launchReceiver()
        val rnd = Random()
        while (System.currentTimeMillis() < deadline) {
            when (rnd.nextInt(3)) {
                0 -> { // cancel & restart sender
                    stopSender()
                    launchSender()
                }
                1 -> { // cancel & restrat receiver
                    stopReceier()
                    launchReceiver()
                }
                2 -> yield() // just yield (burn a little time)
            }
        }
        stopSender()
        stopReceier()
        println("            Sent $lastSent ints to channel")
        println("        Received $lastReceived ints from channel")
        println("  Stopped sender $stoppedSender times")
        println("Stopped receiver $stoppedReceiver times")
        println("          Missed $missedCnt ints")
        println("      Duplicated $dupCnt ints")
        assertEquals(0, missedCnt)
        assertEquals(0, dupCnt)
        assertEquals(lastSent, lastReceived)
    }

    fun launchSender() {
        sender = launch(CommonPool) {
            try {
                while (true) {
                    val trySend = lastSent + 1
                    channel.send(trySend)
                    lastSent = trySend // update on success
                }
            } finally {
                run(NonCancellable) { senderDone.send(true) }
            }
        }
    }

    suspend fun stopSender() {
        stoppedSender++
        sender.cancel()
        senderDone.receive()
    }

    fun launchReceiver() {
        receiver = launch(CommonPool) {
            try {
                while (true) {
                    val received = channel.receive()
                    val expected = lastReceived + 1
                    if (received > expected)
                        missedCnt++
                    if (received < expected)
                        dupCnt++
                    lastReceived = received
                }
            } finally {
                run(NonCancellable) { receiverDone.send(true) }
            }
        }
    }

    suspend fun stopReceier() {
        stoppedReceiver++
        receiver.cancel()
        receiverDone.receive()
    }
}
