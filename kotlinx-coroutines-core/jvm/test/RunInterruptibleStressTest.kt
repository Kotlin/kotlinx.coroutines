/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.*
import org.junit.Test
import java.util.concurrent.atomic.*
import kotlin.test.*

/**
 * Stress test for [runInterruptible].
 * It does not pass on JDK 1.6 on Windows: [Thread.sleep] times out without being interrupted despite the
 * fact that thread interruption flag is set.
 */
class RunInterruptibleStressTest : TestBase() {
    @get:Rule
    val dispatcher = ExecutorRule(4)
    private val repeatTimes = 1000 * stressTestMultiplier

    @Test
    fun testStress() = runTest {
        val enterCount = AtomicInteger(0)
        val interruptedCount = AtomicInteger(0)

        repeat(repeatTimes) {
            val job = launch(dispatcher) {
                try {
                    runInterruptible {
                        enterCount.incrementAndGet()
                        try {
                            Thread.sleep(10_000)
                            error("Sleep was not interrupted, Thread.isInterrupted=${Thread.currentThread().isInterrupted}")
                        } catch (e: InterruptedException) {
                            interruptedCount.incrementAndGet()
                            throw e
                        }
                    }
                } catch (e: CancellationException) {
                    // Expected
                } finally {
                    assertFalse(Thread.currentThread().isInterrupted, "Interrupt flag should not leak")
                }
            }
            // Add dispatch delay
            val cancelJob = launch(dispatcher) {
                job.cancel()
            }
            joinAll(job, cancelJob)
        }
        println("Entered runInterruptible ${enterCount.get()} times")
        assertTrue(enterCount.get() > 0) // ensure timing is Ok and we don't cancel it all prematurely
        assertEquals(enterCount.get(), interruptedCount.get())
    }
}
