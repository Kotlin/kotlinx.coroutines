/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.Test
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.test.*

class DefaultDispatchersTest : TestBase() {

    private /*const*/ val EXPECTED_PARALLELISM = 64

    @Test(timeout = 10_000L)
    fun testLimitedParallelismIsSeparatedFromDefaultIo() = runTest {
        val barrier = CyclicBarrier(EXPECTED_PARALLELISM + 1)
        val ioBlocker = CountDownLatch(1)
        repeat(EXPECTED_PARALLELISM) {
            launch(Dispatchers.IO) {
                barrier.await()
                ioBlocker.await()
            }
        }

        barrier.await() // Ensure all threads are occupied
        barrier.reset()
        val limited = Dispatchers.IO.limitedParallelism(EXPECTED_PARALLELISM)
        repeat(EXPECTED_PARALLELISM) {
            launch(limited) {
                barrier.await()
            }
        }
        barrier.await()
        ioBlocker.countDown()
    }

    @Test(timeout = 10_000L)
    fun testDefaultDispatcherIsSeparateFromIO() = runTest {
        val ioBarrier = CyclicBarrier(EXPECTED_PARALLELISM + 1)
        val ioBlocker = CountDownLatch(1)
        repeat(EXPECTED_PARALLELISM) {
            launch(Dispatchers.IO) {
                ioBarrier.await()
                ioBlocker.await()
            }
        }

        ioBarrier.await() // Ensure all threads are occupied
        val parallelism = Runtime.getRuntime().availableProcessors()
        val defaultBarrier = CyclicBarrier(parallelism + 1)
        repeat(parallelism) {
            launch(Dispatchers.Default) {
                defaultBarrier.await()
            }
        }
        defaultBarrier.await()
        ioBlocker.countDown()
    }

    @Test
    fun testHardCapOnParallelism() = runTest {
        val iterations = 100_000 * stressTestMultiplierSqrt
        val concurrency = AtomicInteger()
        repeat(iterations) {
            launch(Dispatchers.IO) {
                val c = concurrency.incrementAndGet()
                assertTrue("Got: $c") { c <= EXPECTED_PARALLELISM }
                concurrency.decrementAndGet()
            }
        }
    }
}
