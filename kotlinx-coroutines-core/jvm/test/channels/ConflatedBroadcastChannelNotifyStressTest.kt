/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import org.junit.Test
import java.util.concurrent.atomic.*
import kotlin.test.*

class ConflatedBroadcastChannelNotifyStressTest : TestBase() {
    private val nSenders = 2
    private val nReceivers = 3
    private val nEvents = 500_000 * stressTestMultiplier
    private val timeLimit = 30_000L * stressTestMultiplier // 30 sec

    private val broadcast = ConflatedBroadcastChannel<Int>()

    private val sendersCompleted = AtomicInteger()
    private val receiversCompleted = AtomicInteger()
    private val sentTotal = AtomicInteger()
    private val receivedTotal = AtomicInteger()

    @Test
    fun testStressNotify()= runBlocking {
        println("--- ConflatedBroadcastChannelNotifyStressTest")
        val senders = List(nSenders) { senderId ->
            launch(Dispatchers.Default + CoroutineName("Sender$senderId")) {
                repeat(nEvents) { i ->
                    if (i % nSenders == senderId) {
                        broadcast.trySend(i)
                        sentTotal.incrementAndGet()
                        yield()
                    }
                }
                sendersCompleted.incrementAndGet()
            }
        }
        val receivers = List(nReceivers) { receiverId ->
            launch(Dispatchers.Default + CoroutineName("Receiver$receiverId")) {
                var last = -1
                while (isActive) {
                    val i = waitForEvent()
                    if (i > last) {
                        receivedTotal.incrementAndGet()
                        last = i
                    }
                    if (i >= nEvents) break
                    yield()
                }
                receiversCompleted.incrementAndGet()
            }
        }
        // print progress
        val progressJob = launch {
            var seconds = 0
            while (true) {
                delay(1000)
                println("${++seconds}: Sent ${sentTotal.get()}, received ${receivedTotal.get()}")
            }
        }
        try {
            withTimeout(timeLimit) {
                senders.forEach { it.join() }
                broadcast.trySend(nEvents) // last event to signal receivers termination
                receivers.forEach { it.join() }
            }
        } catch (e: CancellationException) {
            println("!!! Test timed out $e")
        }
        progressJob.cancel()
        println("Tested with nSenders=$nSenders, nReceivers=$nReceivers")
        println("Completed successfully ${sendersCompleted.get()} sender coroutines")
        println("Completed successfully ${receiversCompleted.get()} receiver coroutines")
        println("                  Sent ${sentTotal.get()} events")
        println("              Received ${receivedTotal.get()} events")
        assertEquals(nSenders, sendersCompleted.get())
        assertEquals(nReceivers, receiversCompleted.get())
        assertEquals(nEvents, sentTotal.get())
    }

    private suspend fun waitForEvent(): Int =
        with(broadcast.openSubscription()) {
            val value = receive()
            cancel()
            value
        }
}
