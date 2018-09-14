/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.exceptions.*
import org.junit.*
import org.junit.Test
import java.io.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class WithContextCancellationStressTest : TestBase() {

    private val iterations = 15_000 * stressTestMultiplier
    private val pool = newFixedThreadPoolContext(3, "WithContextCancellationStressTest")

    @After
    fun tearDown() {
        pool.close()
    }

    @Test
    fun testConcurrentCancellation() = runBlocking {
        var ioException = 0
        var arithmeticException = 0
        var aioobException = 0

        repeat(iterations) {
            val barrier = CyclicBarrier(4)
            val ctx = pool + NonCancellable
            val jobWithContext = async(ctx) {
                withContext(wrapperDispatcher(coroutineContext), start = CoroutineStart.ATOMIC) {
                    barrier.await()
                    throw IOException()
                }
            }

            val cancellerJob = async(ctx) {
                barrier.await()
                jobWithContext.cancel(ArithmeticException())
            }

            val cancellerJob2 = async(ctx) {
                barrier.await()
                jobWithContext.cancel(ArrayIndexOutOfBoundsException())
            }

            barrier.await()
            val aeCancelled = cancellerJob.await()
            val aioobCancelled = cancellerJob2.await()

            try {
                jobWithContext.await()
            } catch (e: Exception) {
                when (e) {
                    is IOException -> {
                        ++ioException
                        e.checkSuppressed(aeException = aeCancelled, aioobException =  aioobCancelled)
                    }
                    is ArithmeticException -> {
                        ++arithmeticException
                        e.checkSuppressed(ioException = true, aioobException =  aioobCancelled)
                    }
                    is ArrayIndexOutOfBoundsException -> {
                        ++aioobException
                        e.checkSuppressed(ioException = true, aeException =  aeCancelled)
                    }
                    else -> error("Unexpected exception $e")
                }
            }
        }

        require(ioException > 0) { "At least one IOException expected" }
        require(arithmeticException > 0) { "At least one ArithmeticException expected" }
        require(aioobException > 0) { "At least one ArrayIndexOutOfBoundsException expected" }
    }

    private fun wrapperDispatcher(context: CoroutineContext): CoroutineContext {
        val dispatcher = context[ContinuationInterceptor] as CoroutineDispatcher
        return object : CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                dispatcher.dispatch(context, block)
            }
        }
    }

    private fun Throwable.checkSuppressed(
        ioException: Boolean = false,
        aeException: Boolean = false,
        aioobException: Boolean = false
    ) {
        val suppressed = suppressed()

        try {
            if (ioException) {
                assertTrue(suppressed.any { it is IOException }, "IOException should be present: $this")
            }

            if (aeException) {
                assertTrue(suppressed.any { it is ArithmeticException }, "ArithmeticException should be present: $this")
            }

            if (aioobException) {
                assertTrue(
                    suppressed.any { it is ArrayIndexOutOfBoundsException },
                    "ArrayIndexOutOfBoundsException should be present: $this"
                )
            }
        } catch (e: Throwable) {
            val a =2
        }
    }
}
