/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import java.util.concurrent.atomic.*
import kotlin.test.*

class RunInterruptibleStressTest : TestBase() {

    private val dispatcher = Dispatchers.IO
    private val REPEAT_TIMES = 1000 * stressTestMultiplier

    @Test
    fun testStress() = runBlocking {
        val interruptLeak = AtomicBoolean(false)
        val enterCount = AtomicInteger(0)
        val interruptedCount = AtomicInteger(0)
        val otherExceptionCount = AtomicInteger(0)

        repeat(REPEAT_TIMES) { repeat ->
            val job = launch(dispatcher, start = CoroutineStart.LAZY) {
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
                } catch (e: Throwable) {
                    otherExceptionCount.incrementAndGet()
                } finally {
                    interruptLeak.set(interruptLeak.get() || Thread.currentThread().isInterrupted)
                }
            }

            val cancelJob = launch(dispatcher, start = CoroutineStart.LAZY) {
                job.cancel()
            }

            job.start()
            val canceller = launch(dispatcher) {
                cancelJob.start()
            }

            joinAll(job, cancelJob, canceller)
        }

        assertFalse(interruptLeak.get())
        assertEquals(enterCount.get(), interruptedCount.get())
        assertEquals(0, otherExceptionCount.get())
    }
}
