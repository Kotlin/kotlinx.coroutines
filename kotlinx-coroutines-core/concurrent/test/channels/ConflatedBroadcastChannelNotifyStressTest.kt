/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.test.*

class ConflatedBroadcastChannelNotifyStressTest : TestBase() {
    private val nSenders = 2
    private val nReceivers = 3
    private val nEvents =  (if (isNative) 5_000 else 500_000) * stressTestMultiplier
    private val timeLimit = 30_000L * stressTestMultiplier // 30 sec

    private val broadcast = ConflatedBroadcastChannel<Int>()

    private val sendersCompleted = atomic(0)
    private val receiversCompleted = atomic(0)
    private val sentTotal = atomic(0)
    private val receivedTotal = atomic(0)

    @Test
    fun testStressNotify()= runMtTest {
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
                println("${++seconds}: Sent ${sentTotal.value}, received ${receivedTotal.value}")
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
        println("Completed successfully ${sendersCompleted.value} sender coroutines")
        println("Completed successfully ${receiversCompleted.value} receiver coroutines")
        println("                  Sent ${sentTotal.value} events")
        println("              Received ${receivedTotal.value} events")
        assertEquals(nSenders, sendersCompleted.value)
        assertEquals(nReceivers, receiversCompleted.value)
        assertEquals(nEvents, sentTotal.value)
    }

    private suspend fun waitForEvent(): Int =
        with(broadcast.openSubscription()) {
            val value = receive()
            cancel()
            value
        }
}
