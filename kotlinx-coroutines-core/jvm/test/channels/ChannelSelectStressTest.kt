/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import org.junit.After
import org.junit.Test
import java.util.concurrent.atomic.AtomicLongArray
import kotlin.test.*

class ChannelSelectStressTest : TestBase() {
    private val pairedCoroutines = 3
    private val dispatcher = newFixedThreadPoolContext(pairedCoroutines * 2, "ChannelSelectStressTest")
    private val elementsToSend = 20_000 * Long.SIZE_BITS * stressTestMultiplier
    private val sent = atomic(0)
    private val received = atomic(0)
    private val receivedArray = AtomicLongArray(elementsToSend / Long.SIZE_BITS)
    private val channel = Channel<Int>()

    @After
    fun tearDown() {
        dispatcher.close()
    }

    @Test
    fun testAtomicCancelStress() = runTest {
        withContext(dispatcher) {
            repeat(pairedCoroutines) { launchSender() }
            repeat(pairedCoroutines) { launchReceiver() }
        }
        val missing = ArrayList<Int>()
        for (i in 0 until receivedArray.length()) {
            val bits = receivedArray[i]
            if (bits != 0L.inv()) {
                for (j in 0 until Long.SIZE_BITS) {
                    val mask = 1L shl j
                    if (bits and mask == 0L) missing += i * Long.SIZE_BITS + j
                }
            }
        }
        if (missing.isNotEmpty()) {
            fail("Missed ${missing.size} out of $elementsToSend: $missing")
        }
    }

    private fun CoroutineScope.launchSender() {
        launch {
            while (sent.value < elementsToSend) {
                val element = sent.getAndIncrement()
                if (element >= elementsToSend) break
                select<Unit> { channel.onSend(element) {} }
            }
            channel.close(CancellationException())
        }
    }

    private fun CoroutineScope.launchReceiver() {
        launch {
            while (received.value != elementsToSend) {
                val element = select<Int> { channel.onReceive { it } }
                received.incrementAndGet()
                val index = (element / Long.SIZE_BITS)
                val mask = 1L shl (element % Long.SIZE_BITS.toLong()).toInt()
                while (true) {
                    val bits = receivedArray.get(index)
                    if (bits and mask != 0L) {
                        error("Detected duplicate")
                    }
                    if (receivedArray.compareAndSet(index, bits, bits or mask)) break
                }
            }
        }
    }
}
