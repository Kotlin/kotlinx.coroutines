/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.Test
import java.io.IOException
import java.util.concurrent.CountDownLatch
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class CoroutineInterruptibleTest: TestBase() {

    @Test
    fun testNormalRun() = runBlocking(CoroutineInterruptible) {
        var x = async(Dispatchers.Default) {
            doSomethingUsefulCancelable(100L, 13)
        }
        var y = async(Dispatchers.IO) {
            doSomethingUsefulInterruptible(150L, 29)
        }
        assertEquals(42, x.await() + y.await())
    }

    @Test
    fun testInterrupt() {
        val count = AtomicInteger(0)
        try {
            runBlocking {

                launch(Dispatchers.IO + CoroutineInterruptible) {

                    async {
                        try {
                            doSomethingUsefulCancelable(Long.MAX_VALUE, 0)
                        } catch (e: CancellationException) {
                            count.incrementAndGet()
                        }
                    }

                    async {
                        try {
                            // With CoroutineInterruptible, blocking procedures can get stopped
                            // on cancellation (by errors or not)
                            doSomethingUsefulInterruptible(Long.MAX_VALUE, 0)
                        } catch (e: InterruptedException) {
                            count.incrementAndGet()
                        }
                    }

                    async {
                        delay(500L)
                        throw IOException()
                    }
                }
            }
        } catch (e: IOException) {
            count.incrementAndGet()
        }

        assertEquals(3, count.get())
    }

    @Test
    fun testInterruptExceptionTransform() {
        val done = CountDownLatch(1)
        var transformed: Throwable? = null

        val mainScope = MainScope() + Dispatchers.IO + CoroutineInterruptible
        mainScope.launch {
            try {
                // InterruptedException will be transformed to CancellationException at
                // coroutine boundaries with CoroutineInterruptible
                withContext(CoroutineName("exception transform")) {
                    doSomethingUsefulInterruptible(Long.MAX_VALUE, 0)
                }
            } catch (e: Throwable) {
                transformed = e
                throw e
            } finally {
                done.countDown()
            }
        }

        Thread.sleep(500)
        mainScope.cancel()
        done.await()

        assertTrue(transformed is CancellationException)
    }

    @Test
    fun testNoInterruptLeak() = runBlocking {
        var interrupted = true

        var task = launch(Dispatchers.IO) {
            try {
                withContext(CoroutineInterruptible) {
                    doSomethingUsefulInterruptible(Long.MAX_VALUE, 0)
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
                           withContext(CoroutineInterruptible) {
                               enterCount.incrementAndGet()
                               try {
                                   doSomethingUsefulInterruptible(Long.MAX_VALUE, 0)
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

    private suspend fun doSomethingUsefulCancelable(timeUseMillis: Long, result: Int): Int {
        delay(timeUseMillis)
        return result
    }

    private fun doSomethingUsefulInterruptible(timeUseMillis: Long, result: Int): Int {
        Thread.sleep(timeUseMillis)
        return result
    }
}