@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.concurrent.atomics.AtomicInt
import kotlin.concurrent.atomics.ExperimentalAtomicApi
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

@Suppress("DEPRECATION_ERROR")
class ConflatedBroadcastChannelNotifyStressTest : TestBase() {
    private val nSenders = 2
    private val nReceivers = 3
    private val nEvents =  (if (isNative) 5_000 else 500_000) * stressTestMultiplier
    private val timeLimit = 30.seconds * stressTestMultiplier

    private val broadcast = ConflatedBroadcastChannel<Int>()

    private val sendersCompleted = AtomicInt(0)
    private val receiversCompleted = AtomicInt(0)
    private val sentTotal = AtomicInt(0)
    private val receivedTotal = AtomicInt(0)

    @Test
    fun testStressNotify()= runTest {
        println("--- ConflatedBroadcastChannelNotifyStressTest")
        val senders = List(nSenders) { senderId ->
            launch(Dispatchers.Default + CoroutineName("Sender$senderId")) {
                repeat(nEvents) { i ->
                    if (i % nSenders == senderId) {
                        val _ = broadcast.trySend(i)
                        sentTotal.increment()
                        yield()
                    }
                }
                sendersCompleted.increment()
            }
        }
        val receivers = List(nReceivers) { receiverId ->
            launch(Dispatchers.Default + CoroutineName("Receiver$receiverId")) {
                var last = -1
                while (isActive) {
                    val i = waitForEvent()
                    if (i > last) {
                        receivedTotal.increment()
                        last = i
                    }
                    if (i >= nEvents) break
                    yield()
                }
                receiversCompleted.increment()
            }
        }
        // print progress
        val progressJob = launch {
            var seconds = 0
            while (true) {
                delay(1.seconds)
                println("${++seconds}: Sent ${sentTotal.load()}, received ${receivedTotal.load()}")
            }
        }
        try {
            withTimeout(timeLimit) {
                senders.joinAll()
                val _ = broadcast.trySend(nEvents) // last event to signal receivers termination
                receivers.joinAll()
            }
        } catch (e: CancellationException) {
            println("!!! Test timed out $e")
        }
        progressJob.cancel()
        println("Tested with nSenders=$nSenders, nReceivers=$nReceivers")
        println("Completed successfully ${sendersCompleted.load()} sender coroutines")
        println("Completed successfully ${receiversCompleted.load()} receiver coroutines")
        println("                  Sent ${sentTotal.load()} events")
        println("              Received ${receivedTotal.load()} events")
        assertEquals(nSenders, sendersCompleted.load())
        assertEquals(nReceivers, receiversCompleted.load())
        assertEquals(nEvents, sentTotal.load())
    }

    private suspend fun waitForEvent(): Int =
        with(broadcast.openSubscription()) {
            val value = receive()
            cancel()
            value
        }
}
