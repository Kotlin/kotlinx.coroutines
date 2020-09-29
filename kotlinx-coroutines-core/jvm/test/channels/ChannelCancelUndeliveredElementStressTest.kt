/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import java.util.concurrent.atomic.*
import kotlin.random.*
import kotlin.test.*

class ChannelCancelUndeliveredElementStressTest : TestBase() {
    private val repeatTimes = 10_000 * stressTestMultiplier
    private val sendCnt = AtomicInteger(0)
    private val receivedCnt = AtomicInteger(0)
    private val undeliveredCnt = AtomicInteger(0)

    @Test
    fun testStress() = runTest {
        repeat(repeatTimes) {
            val channel = Channel<Unit>(1) { undeliveredCnt.incrementAndGet() }
            val j1 = launch(Dispatchers.Default) {
                sendOne(channel) // send first
                sendOne(channel) // send second
            }
            val j2 = launch(Dispatchers.Default) {
                receiveOne(channel) // receive one element from the channel
                channel.cancel() // cancel the channel
            }

            joinAll(j1, j2)
        }
        // Stats
        println("         Send: ${sendCnt.get()}")
        println("     Received: ${receivedCnt.get()}")
        println("  Undelivered: ${undeliveredCnt.get()}")
        // All elements must be either received or undelivered
        assertEquals(sendCnt.get(), receivedCnt.get() + undeliveredCnt.get())
    }

    private suspend fun sendOne(channel: Channel<Unit>) {
        sendCnt.incrementAndGet()
        when (Random.nextInt(2)) {
            0 -> channel.send(Unit)
            1 -> if (!channel.offer(Unit)) {
                sendCnt.decrementAndGet()
            }
        }
    }

    private suspend fun receiveOne(channel: Channel<Unit>) {
        when (Random.nextInt(3)) {
            0 -> assertEquals(Unit, channel.receive())
            1 -> assertEquals(Unit, channel.receiveOrNull())
            2 -> select<Unit> {
                channel.onReceive { assertEquals(Unit, it) }
            }
        }
        receivedCnt.incrementAndGet()
    }
}