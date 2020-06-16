/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.*
import org.junit.Test
import java.util.concurrent.atomic.*
import kotlin.test.*

class RunInterruptibleStressTest : TestBase() {

    @get:Rule
    val dispatcher = ExecutorRule(4)
    private val REPEAT_TIMES = 1000 * stressTestMultiplier

    @Test
    fun testStress() = runBlocking {
        val interruptLeak = AtomicBoolean(false)
        val enterCount = AtomicInteger(0)
        val interruptedCount = AtomicInteger(0)

        repeat(REPEAT_TIMES) {
            val job = launch(dispatcher) {
                try {
                    runInterruptible {
                        enterCount.incrementAndGet()
                        try {
                            Thread.sleep(Long.MAX_VALUE)
                        } catch (e: InterruptedException) {
                            interruptedCount.incrementAndGet()
                            throw e
                        }
                    }
                } catch (e: CancellationException) {
                    // Expected
                } finally {
                    interruptLeak.set(interruptLeak.get() || Thread.currentThread().isInterrupted)
                }
            }
            // Add dispatch delay
            val cancelJob = launch(dispatcher) {
                job.cancel()
            }

            job.start()
            joinAll(job, cancelJob)
        }

        assertFalse(interruptLeak.get())
        assertEquals(enterCount.get(), interruptedCount.get())
    }
}
