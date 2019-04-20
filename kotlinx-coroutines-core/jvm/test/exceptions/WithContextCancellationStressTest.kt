/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

class WithContextCancellationStressTest : TestBase() {

    private val iterations = 15_000 * stressTestMultiplier
    private val pool = newFixedThreadPoolContext(3, "WithContextCancellationStressTest")

    @After
    fun tearDown() {
        pool.close()
    }

    @Test
    @Suppress("DEPRECATION")
    fun testConcurrentFailure() = runBlocking {
        var eCnt = 0
        var e1Cnt = 0
        var e2Cnt = 0

        repeat(iterations) {
            val barrier = CyclicBarrier(4)
            val ctx = pool + NonCancellable
            var e1 = false
            var e2 = false
            val jobWithContext = async(ctx) {
                withContext(wrapperDispatcher(coroutineContext)) {
                    launch {
                        barrier.await()
                        e1 = true
                        throw TestException1()
                    }

                    launch {
                        barrier.await()
                        e2 = true
                        throw TestException2()
                    }

                    barrier.await()
                    throw TestException()
                }
            }

            barrier.await()

            try {
                jobWithContext.await()
            } catch (e: Throwable) {
                when (e) {
                    is TestException -> {
                        eCnt++
                        e.checkSuppressed(e1 = e1, e2 =  e2)
                    }
                    is TestException1 -> {
                        e1Cnt++
                        e.checkSuppressed(ex = true, e2 = e2)
                    }
                    is TestException2 -> {
                        e2Cnt++
                        e.checkSuppressed(ex = true, e1 = e1)
                    }
                    else -> error("Unexpected exception $e")
                }
            }
        }

        require(eCnt > 0) { "At least one TestException expected" }
        require(e1Cnt > 0) { "At least one TestException1 expected" }
        require(e2Cnt > 0) { "At least one TestException2 expected" }
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
        ex: Boolean = false,
        e1: Boolean = false,
        e2: Boolean = false
    ) {
        val suppressed: Array<Throwable> = suppressed
        if (ex) {
            assertTrue(suppressed.any { it is TestException }, "TestException should be present: $this")
        }
        if (e1) {
            assertTrue(suppressed.any { it is TestException1 }, "TestException1 should be present: $this")
        }
        if (e2) {
            assertTrue(suppressed.any { it is TestException2 }, "TestException2 should be present: $this")
        }
    }
}
