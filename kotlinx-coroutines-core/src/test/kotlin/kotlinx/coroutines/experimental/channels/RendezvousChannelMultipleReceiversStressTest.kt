package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.join
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Test
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class RendezvousChannelMultipleReceiversStressTest {
    val nEvents = 1_000_000
    val nReceivers = 6

    val channel = RendezvousChannel<Int>()
    val completedSuccessfully = AtomicInteger()
    val dupes = AtomicInteger()
    val received = ConcurrentHashMap<Int,Int>()
    val receivedBy = IntArray(nReceivers)

    @Test
    fun testStress() = runBlocking {
        val receivers = List(nReceivers) { receiverIndex ->
            // different event receivers use different code
            launch(CommonPool) {
                when (receiverIndex % 3) {
                    0 -> doReceive(receiverIndex)
                    1 -> doReceiveOrNull(receiverIndex)
                    2 -> doIterator(receiverIndex)
                }
                completedSuccessfully.incrementAndGet()
            }
        }
        repeat(nEvents) {
            channel.send(it)
        }
        channel.close()
        receivers.forEach { it.join() }
        println("Completed successfully ${completedSuccessfully.get()} coroutines")
        println("              Received ${received.size} events")
        println("        Received dupes ${dupes.get()}")
        repeat(nReceivers) { receiveIndex ->
            println("        Received by #$receiveIndex ${receivedBy[receiveIndex]}")
        }
        assertEquals(nReceivers, completedSuccessfully.get())
        assertEquals(0, dupes.get())
        assertEquals(nEvents, received.size)
        repeat(nReceivers) { receiveIndex ->
            assertTrue(receivedBy[receiveIndex] > nEvents / nReceivers / 2, "Should be balanced")
        }
    }

    private fun doReceived(event: Int) {
        if (received.put(event, event) != null) {
            println("Duplicate event $event")
            dupes.incrementAndGet()
        }
    }

    private suspend fun doReceive(receiverIndex: Int) {
        while (true) {
            try { doReceived(channel.receive()) }
            catch (ex: ClosedReceiveChannelException) { break }
            receivedBy[receiverIndex]++
        }

    }

    private suspend fun doReceiveOrNull(receiverIndex: Int) {
        while (true) {
            doReceived(channel.receiveOrNull() ?: break)
            receivedBy[receiverIndex]++
        }
    }

    private suspend fun doIterator(receiverIndex: Int) {
        for (event in channel) {
            doReceived(event)
            receivedBy[receiverIndex]++
        }
    }
}