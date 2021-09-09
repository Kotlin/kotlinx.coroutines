/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.atomic.AtomicLongArray
import kotlin.math.*
import kotlin.test.*

/**
 * Tests lock-freedom of send and receive operations on rendezvous and conflated channels.
 * There is a single channel with two sender and two receiver threads.
 * When one sender or receiver gets suspended at most one other operation is allowed to cease having progress
 * (`allowSuspendedThreads = 1`).
 *
 * **Note**: In the current implementation buffered channels are not lock-free, so this test would fail
 *           if channel is created with a buffer.
 */
class ChannelLFStressTest : TestBase() {
    private val nSeconds = 5 * stressTestMultiplier
    private val env = LockFreedomTestEnvironment("ChannelLFStressTest", allowSuspendedThreads = 1)
    private lateinit var channel: Channel<Long>

    private val sendIndex = AtomicLong()
    private val receiveCount = AtomicLong()
    private val duplicateCount = AtomicLong()

    private val nCheckedSize = 10_000_000
    private val nChecked = (nCheckedSize * Long.SIZE_BITS).toLong()
    private val receivedBits = AtomicLongArray(nCheckedSize) // bit set of received values

    @Test
    fun testRendezvousLockFreedom() {
        channel = Channel()
        performLockFreedomTest()
        // ensure that all sent were received
        checkAllReceived()
    }

    private fun performLockFreedomTest() {
        env.onCompletion {
            // We must cancel the channel to abort both senders & receivers
            channel.cancel(TestCompleted())
        }
        repeat(2) { env.testThread("sender-$it") { sender() } }
        repeat(2) { env.testThread("receiver-$it") { receiver() } }
        env.performTest(nSeconds) {
            println("Sent: $sendIndex, Received: $receiveCount, dups: $duplicateCount")
        }
        // ensure no duplicates
        assertEquals(0L, duplicateCount.get())
    }

    private fun checkAllReceived() {
        for (i in 0 until min(sendIndex.get(), nChecked)) {
            assertTrue(isReceived(i))
        }
    }

    private suspend fun sender() {
        val value = sendIndex.getAndIncrement()
        try {
            channel.send(value)
        } catch (e: TestCompleted) {
            check(env.isCompleted) // expected when test was completed
            markReceived(value) // fake received (actually failed to send)
        }
    }

    private suspend fun receiver() {
        val value = try {
            channel.receive()
        } catch (e: TestCompleted) {
            check(env.isCompleted) // expected when test was completed
            return
        }
        receiveCount.incrementAndGet()
        markReceived(value)
    }

    private fun markReceived(value: Long) {
        if (value >= nChecked) return // too big
        val index = (value / Long.SIZE_BITS).toInt()
        val mask = 1L shl (value % Long.SIZE_BITS).toInt()
        while (true) {
            val bits = receivedBits.get(index)
            if (bits and mask != 0L) {
                duplicateCount.incrementAndGet()
                break
            }
            if (receivedBits.compareAndSet(index, bits, bits or mask)) break
        }
    }

    private fun isReceived(value: Long): Boolean {
        val index = (value / Long.SIZE_BITS).toInt()
        val mask = 1L shl (value % Long.SIZE_BITS).toInt()
        val bits = receivedBits.get(index)
        return bits and mask != 0L
    }

    private class TestCompleted : CancellationException()
}
