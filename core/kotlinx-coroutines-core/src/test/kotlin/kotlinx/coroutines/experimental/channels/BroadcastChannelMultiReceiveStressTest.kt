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
import org.junit.After
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicInteger

/**
 * Tests delivery of events to multiple broadcast channel subscribers.
 */
@RunWith(Parameterized::class)
class BroadcastChannelMultiReceiveStressTest(
    val kind: TestBroadcastChannelKind
) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> =
            TestBroadcastChannelKind.values().map { arrayOf<Any>(it) }
    }

    private val nReceivers = if (isStressTest) 10 else 5
    private val nSeconds = 5 * stressTestMultiplier

    private val broadcast = kind.create()
    private val pool = newFixedThreadPoolContext(nReceivers + 1, "BroadcastChannelMultiReceiveStressTest")

    private val sentTotal = AtomicInteger()
    private val receivedTotal = AtomicInteger()
    private val stopOnReceive = AtomicInteger(-1)
    private val lastReceived = Array(nReceivers) { AtomicInteger(-1) }

    @After
    fun tearDown() {
        pool.cancel()
    }

    @Test
    fun testStress() = runBlocking {
        val ctx = pool + coroutineContext[Job]!!
        val sender =
            launch(context = ctx + CoroutineName("Sender")) {
                while (isActive) {
                    broadcast.send(sentTotal.incrementAndGet())
                }
            }
        val receivers = mutableListOf<Job>()
        repeat(nSeconds) { sec ->
            // launch new receiver up to max
            if (receivers.size < nReceivers) {
                val receiverIndex = receivers.size
                val name = "Receiver$receiverIndex"
                println("$sec: Launching $name")
                receivers += launch(ctx + CoroutineName(name)) {
                    broadcast.openSubscription().use { sub ->
                        when (receiverIndex % 5) {
                            0 -> doReceive(sub, receiverIndex)
                            1 -> doReceiveOrNull(sub, receiverIndex)
                            2 -> doIterator(sub, receiverIndex)
                            3 -> doReceiveSelect(sub, receiverIndex)
                            4 -> doReceiveSelectOrNull(sub, receiverIndex)
                        }
                    }
                }
            }
            // wait a sec
            delay(1000)
            // print progress
            println("${sec + 1}: Sent ${sentTotal.get()}, received ${receivedTotal.get()}, receivers=${receivers.size}")
        }
        sender.cancelAndJoin()
        println("Tested with nReceivers=$nReceivers")
        val total = sentTotal.get()
        println("      Sent $total events, waiting for receivers")
        stopOnReceive.set(total)
        withTimeout(5, TimeUnit.SECONDS) {
            receivers.forEachIndexed { index, receiver ->
                if (lastReceived[index].get() == total)
                    receiver.cancel()
                else
                    receiver.join()
            }
        }
        println("  Received ${receivedTotal.get()} events")
    }

    private fun doReceived(receiverIndex: Int, i: Int): Boolean {
        val last = lastReceived[receiverIndex].get()
        check(i > last) { "Last was $last, got $i" }
        if (last != -1 && !kind.isConflated)
            check(i == last + 1) { "Last was $last, got $i" }
        receivedTotal.incrementAndGet()
        lastReceived[receiverIndex].set(i)
        return i == stopOnReceive.get()
    }

    private suspend fun doReceive(channel: ReceiveChannel<Int>, receiverIndex: Int) {
        while (true) {
            try {
                val stop = doReceived(receiverIndex, channel.receive())
                if (stop) break
            }
            catch (ex: ClosedReceiveChannelException) { break }
        }
    }

    private suspend fun doReceiveOrNull(channel: ReceiveChannel<Int>, receiverIndex: Int) {
        while (true) {
            val stop = doReceived(receiverIndex, channel.receiveOrNull() ?: break)
            if (stop) break
        }
    }

    private suspend fun doIterator(channel: ReceiveChannel<Int>, receiverIndex: Int) {
        for (event in channel) {
            val stop = doReceived(receiverIndex, event)
            if (stop) break
        }
    }

    private suspend fun doReceiveSelect(channel: ReceiveChannel<Int>, receiverIndex: Int) {
        while (true) {
            try {
                val event = select<Int> { channel.onReceive { it } }
                val stop = doReceived(receiverIndex, event)
                if (stop) break
            } catch (ex: ClosedReceiveChannelException) { break }
        }
    }

    private suspend fun doReceiveSelectOrNull(channel: ReceiveChannel<Int>, receiverIndex: Int) {
        while (true) {
            val event = select<Int?> { channel.onReceiveOrNull { it } } ?: break
            val stop = doReceived(receiverIndex, event)
            if (stop) break
        }
    }
}