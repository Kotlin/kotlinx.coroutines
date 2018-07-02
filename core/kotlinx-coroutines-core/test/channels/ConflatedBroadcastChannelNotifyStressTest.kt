/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.hamcrest.MatcherAssert.*
import org.hamcrest.core.*
import org.junit.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.experimental.*

class ConflatedBroadcastChannelNotifyStressTest : TestBase() {
    val nSenders = 2
    val nReceivers = 3
    val nEvents = 1_000_000 * stressTestMultiplier
    val timeLimit = 30_000L * stressTestMultiplier // 30 sec

    val broadcast = ConflatedBroadcastChannel<Int>()

    val sendersCompleted = AtomicInteger()
    val receiversCompleted = AtomicInteger()
    val sentTotal = AtomicInteger()
    val receivedTotal = AtomicInteger()

    @Test
    fun testStressNotify()= runBlocking<Unit> {
        println("--- ConflatedBroadcastChannelNotifyStressTest")
        val senders = List(nSenders) { senderId ->
            launch(CommonPool + CoroutineName("Sender$senderId")) {
                repeat(nEvents) { i ->
                    if (i % nSenders == senderId) {
                        broadcast.offer(i)
                        sentTotal.incrementAndGet()
                        yield()
                    }
                }
                sendersCompleted.incrementAndGet()
            }
        }
        val receivers = List(nReceivers) { receiverId ->
            launch(CommonPool + CoroutineName("Receiver$receiverId")) {
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
        val progressJob = launch(coroutineContext) {
            var seconds = 0
            while (true) {
                delay(1000)
                println("${++seconds}: Sent ${sentTotal.get()}, received ${receivedTotal.get()}")
            }
        }
        try {
            withTimeout(timeLimit) {
                senders.forEach { it.join() }
                broadcast.offer(nEvents) // last event to signal receivers termination
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
        assertThat(sendersCompleted.get(), IsEqual(nSenders))
        assertThat(receiversCompleted.get(), IsEqual(nReceivers))
        assertThat(sentTotal.get(), IsEqual(nEvents))
    }

    suspend fun waitForEvent(): Int =
        with(broadcast.openSubscription()) {
            val value = receive()
            cancel()
            value
        }
}