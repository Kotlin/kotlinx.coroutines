/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.selects.select
import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicIntegerArray

@RunWith(Parameterized::class)
class ChannelSendReceiveStressTest(
    val kind: TestChannelKind,
    val nSenders: Int,
    val nReceivers: Int
) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "{0}, nSenders={1}, nReceivers={2}")
        @JvmStatic
        fun params(): Collection<Array<Any>> =
                listOf(1, 2, 10).flatMap { nSenders ->
                    listOf(1, 10).flatMap { nReceivers ->
                        TestChannelKind.values().map { arrayOf<Any>(it, nSenders, nReceivers) }
                    }
                }
    }

    val timeLimit = 30_000L * stressTestMultiplier // 30 sec
    val nEvents = 200_000 * stressTestMultiplier

    val maxBuffer = 10_000 // artificial limit for LinkedListChannel

    val channel = kind.create()
    val sendersCompleted = AtomicInteger()
    val receiversCompleted = AtomicInteger()
    val dupes = AtomicInteger()
    val sentTotal = AtomicInteger()
    val received = AtomicIntegerArray(nEvents)
    val receivedTotal = AtomicInteger()
    val receivedBy = IntArray(nReceivers)

    @Test
    fun testSendReceiveStress() = runBlocking {
        println("-------------------------------------")
        println("Testing $kind with nSenders=$nSenders, nReceivers=$nReceivers")
        val receivers = List(nReceivers) { receiverIndex ->
            // different event receivers use different code
            launch(CommonPool + CoroutineName("receiver$receiverIndex")) {
                when (receiverIndex % 5) {
                    0 -> doReceive(receiverIndex)
                    1 -> doReceiveOrNull(receiverIndex)
                    2 -> doIterator(receiverIndex)
                    3 -> doReceiveSelect(receiverIndex)
                    4 -> doReceiveSelectOrNull(receiverIndex)
                }
                receiversCompleted.incrementAndGet()
            }
        }
        val senders = List(nSenders) { senderIndex ->
            launch(CommonPool + CoroutineName("sender$senderIndex")) {
                when (senderIndex % 2) {
                    0 -> doSend(senderIndex)
                    1 -> doSendSelect(senderIndex)
                }
                sendersCompleted.incrementAndGet()
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
                channel.close()
                receivers.forEach { it.join() }
            }
        } catch (e: CancellationException) {
            println("!!! Test timed out $e")
        }
        progressJob.cancel()
        println("Tested $kind with nSenders=$nSenders, nReceivers=$nReceivers")
        println("Completed successfully ${sendersCompleted.get()} sender coroutines")
        println("Completed successfully ${receiversCompleted.get()} receiver coroutines")
        println("                  Sent ${sentTotal.get()} events")
        println("              Received ${receivedTotal.get()} events")
        println("        Received dupes ${dupes.get()}")
        repeat(nReceivers) { receiveIndex ->
            println("        Received by #$receiveIndex ${receivedBy[receiveIndex]}")
        }
        assertEquals(nSenders, sendersCompleted.get())
        assertEquals(nReceivers, receiversCompleted.get())
        assertEquals(0, dupes.get())
        assertEquals(nEvents, sentTotal.get())
        if (!kind.isConflated) assertEquals(nEvents, receivedTotal.get())
        repeat(nReceivers) { receiveIndex ->
            assertTrue("Each receiver should have received something", receivedBy[receiveIndex] > 0)
        }
    }

    private suspend fun doSent() {
        sentTotal.incrementAndGet()
        if (!kind.isConflated) {
            while (sentTotal.get() > receivedTotal.get() + maxBuffer)
                yield() // throttle fast senders to prevent OOM with LinkedListChannel
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
            select<Unit> { channel.onSend(i) { Unit } }
            doSent()
        }
    }

    private fun doReceived(receiverIndex: Int, event: Int) {
        if (!received.compareAndSet(event, 0, 1)) {
            println("Duplicate event $event at $receiverIndex")
            dupes.incrementAndGet()
        }
        receivedTotal.incrementAndGet()
        receivedBy[receiverIndex]++
    }

    private suspend fun doReceive(receiverIndex: Int) {
        while (true) {
            try { doReceived(receiverIndex, channel.receive()) }
            catch (ex: ClosedReceiveChannelException) { break }
        }
    }

    private suspend fun doReceiveOrNull(receiverIndex: Int) {
        while (true) {
            doReceived(receiverIndex, channel.receiveOrNull() ?: break)
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
                val event = select<Int> { channel.onReceive { it } }
                doReceived(receiverIndex, event)
            } catch (ex: ClosedReceiveChannelException) { break }
        }
    }

    private suspend fun doReceiveSelectOrNull(receiverIndex: Int) {
        while (true) {
            val event = select<Int?> { channel.onReceiveOrNull { it } } ?: break
            doReceived(receiverIndex, event)
        }
    }
}