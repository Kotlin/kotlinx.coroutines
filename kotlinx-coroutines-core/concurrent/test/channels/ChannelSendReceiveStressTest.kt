@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.testing.*
import kotlin.concurrent.atomics.*
import kotlin.test.*

// kind TestChannelKind
// nSenders 1 2 10
// nReceivers 1 10

// RENDEZVOUS
class ChannelSendReceiveStressTestRENDEZVOUSx1x1 : ChannelSendReceiveStressTest(TestChannelKind.RENDEZVOUS, 1, 1)
class ChannelSendReceiveStressTestRENDEZVOUSx1x10 : ChannelSendReceiveStressTest(TestChannelKind.RENDEZVOUS, 1, 10)
class ChannelSendReceiveStressTestRENDEZVOUSx2x1 : ChannelSendReceiveStressTest(TestChannelKind.RENDEZVOUS, 2, 1)
class ChannelSendReceiveStressTestRENDEZVOUSx2x10 : ChannelSendReceiveStressTest(TestChannelKind.RENDEZVOUS, 2, 10)
class ChannelSendReceiveStressTestRENDEZVOUSx10x1 : ChannelSendReceiveStressTest(TestChannelKind.RENDEZVOUS, 10, 1)
class ChannelSendReceiveStressTestRENDEZVOUSx10x10 : ChannelSendReceiveStressTest(TestChannelKind.RENDEZVOUS, 10, 10)

// BUFFERED_1
class ChannelSendReceiveStressTestBUFFERED1x1x1 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_1, 1, 1)
class ChannelSendReceiveStressTestBUFFERED1x1x10 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_1, 1, 10)
class ChannelSendReceiveStressTestBUFFERED1x2x1 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_1, 2, 1)
class ChannelSendReceiveStressTestBUFFERED1x2x10 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_1, 2, 10)
class ChannelSendReceiveStressTestBUFFERED1x10x1 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_1, 10, 1)
class ChannelSendReceiveStressTestBUFFERED1x10x10 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_1, 10, 10)

// BUFFERED_2
class ChannelSendReceiveStressTestBUFFERED2x1x1 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_2, 1, 1)
class ChannelSendReceiveStressTestBUFFERED2x1x10 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_2, 1, 10)
class ChannelSendReceiveStressTestBUFFERED2x2x1 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_2, 2, 1)
class ChannelSendReceiveStressTestBUFFERED2x2x10 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_2, 2, 10)
class ChannelSendReceiveStressTestBUFFERED2x10x1 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_2, 10, 1)
class ChannelSendReceiveStressTestBUFFERED2x10x10 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_2, 10, 10)

// BUFFERED_10
class ChannelSendReceiveStressTestBUFFERED10x1x1 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_10, 1, 1)
class ChannelSendReceiveStressTestBUFFERED10x1x10 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_10, 1, 10)
class ChannelSendReceiveStressTestBUFFERED10x2x1 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_10, 2, 1)
class ChannelSendReceiveStressTestBUFFERED10x2x10 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_10, 2, 10)
class ChannelSendReceiveStressTestBUFFERED10x10x1 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_10, 10, 1)
class ChannelSendReceiveStressTestBUFFERED10x10x10 : ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_10, 10, 10)

// UNLIMITED
class ChannelSendReceiveStressTestUNLIMITEDx1x1 : ChannelSendReceiveStressTest(TestChannelKind.UNLIMITED, 1, 1)
class ChannelSendReceiveStressTestUNLIMITEDx1x10 : ChannelSendReceiveStressTest(TestChannelKind.UNLIMITED, 1, 10)
class ChannelSendReceiveStressTestUNLIMITEDx2x1 : ChannelSendReceiveStressTest(TestChannelKind.UNLIMITED, 2, 1)
class ChannelSendReceiveStressTestUNLIMITEDx2x10 : ChannelSendReceiveStressTest(TestChannelKind.UNLIMITED, 2, 10)
class ChannelSendReceiveStressTestUNLIMITEDx10x1 : ChannelSendReceiveStressTest(TestChannelKind.UNLIMITED, 10, 1)
class ChannelSendReceiveStressTestUNLIMITEDx10x10 : ChannelSendReceiveStressTest(TestChannelKind.UNLIMITED, 10, 10)

// CONFLATED
class ChannelSendReceiveStressTestCONFLATEDx1x1 : ChannelSendReceiveStressTest(TestChannelKind.CONFLATED, 1, 1)
class ChannelSendReceiveStressTestCONFLATEDx1x10 : ChannelSendReceiveStressTest(TestChannelKind.CONFLATED, 1, 10)
class ChannelSendReceiveStressTestCONFLATEDx2x1 : ChannelSendReceiveStressTest(TestChannelKind.CONFLATED, 2, 1)
class ChannelSendReceiveStressTestCONFLATEDx2x10 : ChannelSendReceiveStressTest(TestChannelKind.CONFLATED, 2, 10)
class ChannelSendReceiveStressTestCONFLATEDx10x1 : ChannelSendReceiveStressTest(TestChannelKind.CONFLATED, 10, 1)
class ChannelSendReceiveStressTestCONFLATEDx10x10 : ChannelSendReceiveStressTest(TestChannelKind.CONFLATED, 10, 10)

// BUFFERED_1_BROADCAST
class ChannelSendReceiveStressTestBUFFERED1BROADCASTx1x1 :
    ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_1_BROADCAST, 1, 1)

class ChannelSendReceiveStressTestBUFFERED1BROADCASTx1x10 :
    ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_1_BROADCAST, 1, 10)

class ChannelSendReceiveStressTestBUFFERED1BROADCASTx2x1 :
    ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_1_BROADCAST, 2, 1)

class ChannelSendReceiveStressTestBUFFERED1BROADCASTx2x10 :
    ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_1_BROADCAST, 2, 10)

class ChannelSendReceiveStressTestBUFFERED1BROADCASTx10x1 :
    ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_1_BROADCAST, 10, 1)

class ChannelSendReceiveStressTestBUFFERED1BROADCASTx10x10 :
    ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_1_BROADCAST, 10, 10)

// BUFFERED_10_BROADCAST
class ChannelSendReceiveStressTestBUFFERED10BROADCASTx1x1 :
    ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_10_BROADCAST, 1, 1)

class ChannelSendReceiveStressTestBUFFERED10BROADCASTx1x10 :
    ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_10_BROADCAST, 1, 10)

class ChannelSendReceiveStressTestBUFFERED10BROADCASTx2x1 :
    ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_10_BROADCAST, 2, 1)

class ChannelSendReceiveStressTestBUFFERED10BROADCASTx2x10 :
    ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_10_BROADCAST, 2, 10)

class ChannelSendReceiveStressTestBUFFERED10BROADCASTx10x1 :
    ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_10_BROADCAST, 10, 1)

class ChannelSendReceiveStressTestBUFFERED10BROADCASTx10x10 :
    ChannelSendReceiveStressTest(TestChannelKind.BUFFERED_10_BROADCAST, 10, 10)

// CONFLATED_BROADCAST
class ChannelSendReceiveStressTestCONFLATEDBROADCASTx1x1 :
    ChannelSendReceiveStressTest(TestChannelKind.CONFLATED_BROADCAST, 1, 1)

class ChannelSendReceiveStressTestCONFLATEDBROADCASTx1x10 :
    ChannelSendReceiveStressTest(TestChannelKind.CONFLATED_BROADCAST, 1, 10)

class ChannelSendReceiveStressTestCONFLATEDBROADCASTx2x1 :
    ChannelSendReceiveStressTest(TestChannelKind.CONFLATED_BROADCAST, 2, 1)

class ChannelSendReceiveStressTestCONFLATEDBROADCASTx2x10 :
    ChannelSendReceiveStressTest(TestChannelKind.CONFLATED_BROADCAST, 2, 10)

class ChannelSendReceiveStressTestCONFLATEDBROADCASTx10x1 :
    ChannelSendReceiveStressTest(TestChannelKind.CONFLATED_BROADCAST, 10, 1)

class ChannelSendReceiveStressTestCONFLATEDBROADCASTx10x10 :
    ChannelSendReceiveStressTest(TestChannelKind.CONFLATED_BROADCAST, 10, 10)

@Ignore
abstract class ChannelSendReceiveStressTest(
    private val kind: TestChannelKind,
    private val nSenders: Int,
    private val nReceivers: Int
) : TestBase() {
    private val timeLimit = 30_000L * stressTestMultiplier // 30 sec
    private val nEvents = 200_000 * stressTestMultiplier

    private val maxBuffer = 10_000 // artificial limit for unlimited channel

    val channel = kind.create<Int>()
    private val sendersCompleted = AtomicInt(0)
    private val receiversCompleted = AtomicInt(0)
    private val dupes = AtomicInt(0)
    private val sentTotal = AtomicInt(0)
    val received = AtomicIntArray(nEvents)
    private val receivedTotal = AtomicInt(0)
    private val receivedBy = IntArray(nReceivers)

    private val pool =
        newFixedThreadPoolContext(nSenders + nReceivers, "ChannelSendReceiveStressTest")

    @AfterTest
    fun tearDown() {
        pool.close()
    }

    @Test
    fun testSendReceiveStress() = runBlocking {
        println("--- ChannelSendReceiveStressTest $kind with nSenders=$nSenders, nReceivers=$nReceivers")
        val receivers = List(nReceivers) { receiverIndex ->
            // different event receivers use different code
            launch(pool + CoroutineName("receiver$receiverIndex")) {
                when (receiverIndex % 5) {
                    0 -> doReceive(receiverIndex)
                    1 -> doReceiveCatching(receiverIndex)
                    2 -> doIterator(receiverIndex)
                    3 -> doReceiveSelect(receiverIndex)
                    4 -> doReceiveCatchingSelect(receiverIndex)
                }
                receiversCompleted.incrementAndFetch()
            }
        }
        val senders = List(nSenders) { senderIndex ->
            launch(pool + CoroutineName("sender$senderIndex")) {
                when (senderIndex % 2) {
                    0 -> doSend(senderIndex)
                    1 -> doSendSelect(senderIndex)
                }
                sendersCompleted.incrementAndFetch()
            }
        }
        // print progress
        val progressJob = launch {
            var seconds = 0
            while (true) {
                delay(1000)
                println("${++seconds}: Sent ${sentTotal.load()}, received ${receivedTotal.load()}")
            }
        }
        try {
            withTimeout(timeLimit) {
                senders.joinAll()
                channel.close()
                receivers.joinAll()
            }
        } catch (e: CancellationException) {
            println("!!! Test timed out $e")
        }
        progressJob.cancel()
        println("Tested $kind with nSenders=$nSenders, nReceivers=$nReceivers")
        println("Completed successfully ${sendersCompleted.load()} sender coroutines")
        println("Completed successfully ${receiversCompleted.load()} receiver coroutines")
        println("                  Sent ${sentTotal.load()} events")
        println("              Received ${receivedTotal.load()} events")
        println("        Received dupes ${dupes.load()}")
        repeat(nReceivers) { receiveIndex ->
            println("        Received by #$receiveIndex ${receivedBy[receiveIndex]}")
        }
        (channel as? BufferedChannel<*>)?.checkSegmentStructureInvariants()
        assertEquals(nSenders, sendersCompleted.load())
        assertEquals(nReceivers, receiversCompleted.load())
        assertEquals(0, dupes.load())
        assertEquals(nEvents, sentTotal.load())
        if (!kind.isConflated) assertEquals(nEvents, receivedTotal.load())
        repeat(nReceivers) { receiveIndex ->
            assertTrue(receivedBy[receiveIndex] > 0, "Each receiver should have received something")
        }
    }

    private suspend fun doSent() {
        sentTotal.incrementAndFetch()
        if (!kind.isConflated) {
            while (sentTotal.load() > receivedTotal.load() + maxBuffer)
                yield() // throttle fast senders to prevent OOM with an unlimited channel
        }
    }

    private suspend fun doSend(senderIndex: Int) {
        for (i in senderIndex until nEvents step nSenders) {
            channel.send(i)
            doSent()
        }
    }

    private suspend fun doSendSelect(senderIndex: Int) {
        for (i in senderIndex until nEvents step nSenders) {
            select { channel.onSend(i) { } }
            doSent()
        }
    }

    private fun doReceived(receiverIndex: Int, event: Int) {
        if (!received.compareAndSetAt(event, 0, 1)) {
            println("Duplicate event $event at $receiverIndex")
            dupes.incrementAndFetch()
        }
        receivedTotal.incrementAndFetch()
        receivedBy[receiverIndex]++
    }

    private suspend fun doReceive(receiverIndex: Int) {
        while (true) {
            try {
                doReceived(receiverIndex, channel.receive())
            } catch (_: ClosedReceiveChannelException) {
                break
            }
        }
    }

    private suspend fun doReceiveCatching(receiverIndex: Int) {
        while (true) {
            doReceived(receiverIndex, channel.receiveCatching().getOrNull() ?: break)
        }
    }

    private suspend fun doIterator(receiverIndex: Int) {
        for (event in channel) {
            doReceived(receiverIndex, event)
        }
    }

    private suspend fun doReceiveSelect(receiverIndex: Int) {
        while (true) {
            try {
                val event = select { channel.onReceive { it } }
                doReceived(receiverIndex, event)
            } catch (_: ClosedReceiveChannelException) {
                break
            }
        }
    }

    private suspend fun doReceiveCatchingSelect(receiverIndex: Int) {
        while (true) {
            val event = select<Int?> { channel.onReceiveCatching { it.getOrNull() } } ?: break
            doReceived(receiverIndex, event)
        }
    }
}
