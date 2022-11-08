/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import org.junit.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import java.util.concurrent.atomic.*
import kotlin.test.*

@RunWith(Parameterized::class)
class ChannelSendReceiveStressTest(
    private val kind: TestChannelKind,
    private val nSenders: Int,
    private val nReceivers: Int
) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "{0}, nSenders={1}, nReceivers={2}")
        @JvmStatic
        fun params(): Collection<Array<Any>> =
                listOf(1, 2, 10).flatMap { nSenders ->
                    listOf(1, 10).flatMap { nReceivers ->
                        TestChannelKind.values()
                            // Workaround for bug that won't be fixed unless new channel implementation, see #2443
                            .filter { it != TestChannelKind.LINKED_LIST }
                            .map { arrayOf(it, nSenders, nReceivers) }
                    }
                }
    }

    private val timeLimit = 30_000L * stressTestMultiplier // 30 sec
    private val nEvents = 200_000 * stressTestMultiplier

    private val maxBuffer = 10_000 // artificial limit for LinkedListChannel

    val channel = kind.create<Int>()
    private val sendersCompleted = AtomicInteger()
    private val receiversCompleted = AtomicInteger()
    private val dupes = AtomicInteger()
    private val sentTotal = AtomicInteger()
    val received = AtomicIntegerArray(nEvents)
    private val receivedTotal = AtomicInteger()
    private val receivedBy = IntArray(nReceivers)

    private val pool =
        newFixedThreadPoolContext(nSenders + nReceivers, "ChannelSendReceiveStressTest")

    @After
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
                receiversCompleted.incrementAndGet()
            }
        }
        val senders = List(nSenders) { senderIndex ->
            launch(pool + CoroutineName("sender$senderIndex")) {
                when (senderIndex % 2) {
                    0 -> doSend(senderIndex)
                    1 -> doSendSelect(senderIndex)
                }
                sendersCompleted.incrementAndGet()
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
            assertTrue(receivedBy[receiveIndex] > 0, "Each receiver should have received something")
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
                val event = select<Int> { channel.onReceive { it } }
                doReceived(receiverIndex, event)
            } catch (ex: ClosedReceiveChannelException) { break }
        }
    }

    private suspend fun doReceiveCatchingSelect(receiverIndex: Int) {
        while (true) {
            val event = select<Int?> { channel.onReceiveCatching { it.getOrNull() } } ?: break
            doReceived(receiverIndex, event)
        }
    }
}
