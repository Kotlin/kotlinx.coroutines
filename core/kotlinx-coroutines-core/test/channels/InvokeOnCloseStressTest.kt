/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.*
import kotlin.test.*

class InvokeOnCloseStressTest : TestBase(), CoroutineScope {

    private val iterations = 1000 * stressTestMultiplier

    private val pool = newFixedThreadPoolContext(3, "InvokeOnCloseStressTest")
    override val coroutineContext: CoroutineContext
        get() = pool

    @After
    fun tearDown() {
        pool.close()
    }

    @Test
    fun testInvokedExactlyOnce() = runBlocking {
        runStressTest(TestChannelKind.ARRAY_1)
    }

    @Test
    fun testInvokedExactlyOnceBroadcast() = runBlocking {
        runStressTest(TestChannelKind.CONFLATED_BROADCAST)
    }

    private suspend fun runStressTest(kind: TestChannelKind) {
        repeat(iterations) {
            val counter = AtomicInteger(0)
            val channel = kind.create()

            val latch = CountDownLatch(1)
            val j1 = async {
                latch.await()
                channel.close()
            }

            val j2 = async {
                latch.await()
                channel.invokeOnClose { counter.incrementAndGet() }
            }

            val j3 = async {
                latch.await()
                channel.invokeOnClose { counter.incrementAndGet() }
            }

            latch.countDown()
            joinAll(j1, j2, j3)
            assertEquals(1, counter.get())
        }
    }
}
