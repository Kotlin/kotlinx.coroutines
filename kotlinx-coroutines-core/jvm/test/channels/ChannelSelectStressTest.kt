/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import org.junit.*
import org.junit.Assert.*
import java.util.concurrent.atomic.AtomicLongArray

class ChannelSelectStressTest : TestBase() {
    private val pairedCoroutines = 3
    private val dispatcher = newFixedThreadPoolContext(pairedCoroutines * 2, "ChannelSelectStressTest")
    private val scope = CoroutineScope(dispatcher)
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
        repeat(pairedCoroutines) { launchSender() }
        repeat(pairedCoroutines) { launchReceiver() }
        val job = scope.coroutineContext[Job] as CompletableJob
        job.complete()
        job.join()

        for (i in 0 until receivedArray.length()) {
            assertEquals("Missing element detected", 0L.inv(), receivedArray[i])
        }
    }

    private fun launchSender() {
        scope.launch {
            while (sent.value < elementsToSend) {
                val element = sent.getAndIncrement()
                if (element >= elementsToSend) break
                select<Unit> { channel.onSend(element) {} }
            }
            channel.close(CancellationException())
        }
    }

    private fun launchReceiver() {
        scope.launch {
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
