/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.Test
import java.util.concurrent.*
import java.util.concurrent.atomic.AtomicInteger

class CoroutineSchedulerOversubscriptionTest : TestBase() {

    private val inDefault = AtomicInteger(0)

    private fun CountDownLatch.runAndCheck() {
        if (inDefault.incrementAndGet() > CORE_POOL_SIZE) {
            error("Oversubscription detected")
        }

        await()
        inDefault.decrementAndGet()
    }

    @Test
    fun testOverSubscriptionDeterministic() = runTest {
        val barrier = CountDownLatch(1)
        val threadsOccupiedBarrier = CyclicBarrier(CORE_POOL_SIZE)
        // All threads but one
        repeat(CORE_POOL_SIZE - 1) {
            launch(Dispatchers.Default) {
                threadsOccupiedBarrier.await()
                barrier.runAndCheck()
            }
        }
        threadsOccupiedBarrier.await()
        withContext(Dispatchers.Default) {
            // Put a task in a local queue, it will be stolen
            launch(Dispatchers.Default) {
                barrier.runAndCheck()
            }
            // Put one more task to trick the local queue check
            launch(Dispatchers.Default) {
                barrier.runAndCheck()
            }

            withContext(Dispatchers.IO) {
                try {
                    // Release the thread
                    delay(100)
                } finally {
                    barrier.countDown()
                }
            }
        }
    }

    @Test
    fun testOverSubscriptionStress() = repeat(1000 * stressTestMultiplierSqrt) {
        inDefault.set(0)
        runTest {
            val barrier = CountDownLatch(1)
            val threadsOccupiedBarrier = CyclicBarrier(CORE_POOL_SIZE)
            // All threads but one
            repeat(CORE_POOL_SIZE - 1) {
                launch(Dispatchers.Default) {
                    threadsOccupiedBarrier.await()
                    barrier.runAndCheck()
                }
            }
            threadsOccupiedBarrier.await()
            withContext(Dispatchers.Default) {
                // Put a task in a local queue
                launch(Dispatchers.Default) {
                    barrier.runAndCheck()
                }
                // Put one more task to trick the local queue check
                launch(Dispatchers.Default) {
                    barrier.runAndCheck()
                }

                withContext(Dispatchers.IO) {
                    yield()
                    barrier.countDown()
                }
            }
        }
    }
}
