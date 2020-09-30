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

    // total counters
    private var sendCnt = 0
    private var offerFailedCnt = 0
    private var receivedCnt = 0
    private var undeliveredCnt = 0

    // last operation
    private var lastReceived = 0
    private var dSendCnt = 0
    private var dSendExceptionCnt = 0
    private var dOfferFailedCnt = 0
    private var dReceivedCnt = 0
    private val dUndeliveredCnt = AtomicInteger()

    @Test
    fun testStress() = runTest {
        repeat(repeatTimes) {
            val channel = Channel<Int>(1) { dUndeliveredCnt.incrementAndGet() }
            val j1 = launch(Dispatchers.Default) {
                sendOne(channel) // send first
                sendOne(channel) // send second
            }
            val j2 = launch(Dispatchers.Default) {
                receiveOne(channel) // receive one element from the channel
                channel.cancel() // cancel the channel
            }

            joinAll(j1, j2)

            // All elements must be either received or undelivered (IN every run)
            if (dSendCnt - dOfferFailedCnt != dReceivedCnt + dUndeliveredCnt.get()) {
                println("          Send: $dSendCnt")
                println("Send Exception: $dSendExceptionCnt")
                println("  Offer failed: $dOfferFailedCnt")
                println("      Received: $dReceivedCnt")
                println("   Undelivered: ${dUndeliveredCnt.get()}")
                error("Failed")
            }
            offerFailedCnt += dOfferFailedCnt
            receivedCnt += dReceivedCnt
            undeliveredCnt += dUndeliveredCnt.get()
            // clear for next run
            dSendCnt = 0
            dSendExceptionCnt = 0
            dOfferFailedCnt = 0
            dReceivedCnt = 0
            dUndeliveredCnt.set(0)
        }
        // Stats
        println("         Send: $sendCnt")
        println(" Offer failed: $offerFailedCnt")
        println("     Received: $receivedCnt")
        println("  Undelivered: $undeliveredCnt")
        assertEquals(sendCnt - offerFailedCnt, receivedCnt + undeliveredCnt)
    }

    private suspend fun sendOne(channel: Channel<Int>) {
        dSendCnt++
        val i = ++sendCnt
        try {
            when (Random.nextInt(2)) {
                0 -> channel.send(i)
                1 -> if (!channel.offer(i)) {
                    dOfferFailedCnt++
                }
            }
        } catch(e: Throwable) {
            assertTrue(e is CancellationException) // the only exception possible in this test
            dSendExceptionCnt++
            throw e
        }
    }

    private suspend fun receiveOne(channel: Channel<Int>) {
        val received = when (Random.nextInt(3)) {
            0 -> channel.receive()
            1 -> channel.receiveOrNull() ?: error("Cannot be closed yet")
            2 -> select {
                channel.onReceive { it }
            }
            else -> error("Cannot happen")
        }
        assertTrue(received > lastReceived)
        dReceivedCnt++
        lastReceived = received
    }
}