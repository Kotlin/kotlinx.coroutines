/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import java.io.IOException
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import kotlin.test.*

class InterruptibleTest: TestBase() {
    @Test
    fun testNormalRun() = runBlocking {
        var result = runInterruptible {
            var x = doSomethingUsefulBlocking(1, 1)
            var y = doSomethingUsefulBlocking(1, 2)
            x + y
        }
        assertEquals(3, result)
    }

    @Test
    fun testExceptionThrow() = runBlocking {
        try {
            runInterruptible {
                throw TestException()
            }
        } catch (e: Throwable) {
            assertTrue(e is TestException)
            return@runBlocking
        }
        fail()
    }

    @Test
    fun testRunWithContext() = runBlocking {
        var runThread =
                runInterruptible (Dispatchers.IO) {
                    Thread.currentThread()
                }
        assertNotEquals(runThread, Thread.currentThread())
    }

    @Test
    fun testInterrupt() {
        val count = AtomicInteger(0)
        try {
            expect(1)
            runBlocking {
                launch(Dispatchers.IO) {
                    async {
                        try {
                            // `runInterruptible` makes a blocking block cancelable (become a cancellation point)
                            // by interrupting it on cancellation and throws CancellationException
                            runInterruptible {
                                try {
                                    doSomethingUsefulBlocking(100, 1)
                                    doSomethingUsefulBlocking(Long.MAX_VALUE, 0)
                                } catch (e: InterruptedException) {
                                    expect(3)
                                    throw e
                                }
                            }
                        } catch (e: CancellationException) {
                            expect(4)
                        }
                    }

                    async {
                        delay(500L)
                        expect(2)
                        throw IOException()
                    }
                }
            }
        } catch (e: IOException) {
            expect(5)
        }
        finish(6)
    }

    @Test
    fun testNoInterruptLeak() = runBlocking {
        var interrupted = true

        var task = launch(Dispatchers.IO) {
            try {
                runInterruptible {
                    doSomethingUsefulBlocking(Long.MAX_VALUE, 0)
                }
            } finally {
                interrupted = Thread.currentThread().isInterrupted
            }
        }

        delay(500)
        task.cancel()
        task.join()
        assertFalse(interrupted)
    }

    @Test
    fun testStress() {
        val REPEAT_TIMES = 2_000

        Executors.newCachedThreadPool().asCoroutineDispatcher().use { dispatcher ->
            val interruptLeak = AtomicBoolean(false)
            val enterCount = AtomicInteger(0)
            val interruptedCount = AtomicInteger(0)
            val otherExceptionCount = AtomicInteger(0)

            runBlocking {
               repeat(REPEAT_TIMES) { repeat ->
                   var job = launch(start = CoroutineStart.LAZY, context = dispatcher) {
                       try {
                           runInterruptible {
                               enterCount.incrementAndGet()
                               try {
                                   doSomethingUsefulBlocking(Long.MAX_VALUE, 0)
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

                   var cancelJob = launch(start = CoroutineStart.LAZY, context = dispatcher) {
                       job.cancel()
                   }

                   launch (dispatcher) {
                       delay((REPEAT_TIMES - repeat).toLong())
                       job.start()
                   }

                   launch (dispatcher) {
                       delay(repeat.toLong())
                       cancelJob.start()
                   }
               }
            }

            assertFalse(interruptLeak.get())
            assertEquals(enterCount.get(), interruptedCount.get())
            assertEquals(0, otherExceptionCount.get())
        }
    }

    private fun doSomethingUsefulBlocking(timeUseMillis: Long, result: Int): Int {
        Thread.sleep(timeUseMillis)
        return result
    }

    private class TestException : Exception()
}
