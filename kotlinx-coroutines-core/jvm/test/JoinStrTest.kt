/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class JoinStressTest : TestBase() {

    private val iterations = 50_000 * stressTestMultiplier
    private val pool = newFixedThreadPoolContext(3, "JoinStressTest")

    @After
    fun tearDown() {
        pool.close()
    }

    @Test
    fun testExceptionalJoinWithCancellation() = runBlocking {
        val results = IntArray(2)

        repeat(iterations) {
            val barrier = CyclicBarrier(3)
            val exceptionalJob = async(pool + NonCancellable) {
                barrier.await()
                throw TestException()
            }


            val awaiterJob = async(pool) {
                barrier.await()
                try {
                    exceptionalJob.await()
                } catch (e: TestException) {
                    0
                } catch (e: CancellationException) {
                    1
                }
            }

            barrier.await()
            exceptionalJob.cancel()
            ++results[awaiterJob.await()]
        }

        // Check that concurrent cancellation of job which throws TestException without suspends doesn't suppress TestException
        assertEquals(iterations, results[0], results.toList().toString())
        assertEquals(0, results[1], results.toList().toString())
    }

    @Test
    fun testExceptionalJoinWithMultipleCancellations() = runBlocking {
        val results = IntArray(2)

        repeat(iterations) {
            val barrier = CyclicBarrier(4)
            val exceptionalJob = async<Unit>(pool + NonCancellable) {
                barrier.await()
                throw TestException()
            }

            val awaiterJob = async(pool) {
                barrier.await()
                try {
                    exceptionalJob.await()
                    2
                } catch (e: TestException) {
                    0
                } catch (e: TestException1) {
                    1
                }
            }

            val canceller = async(pool + NonCancellable) {
                barrier.await()
                // cast for test purposes only
                (exceptionalJob as AbstractCoroutine<*>).cancelInternal(TestException1())
            }

            barrier.await()
            val awaiterResult = awaiterJob.await()
            canceller.await()
            ++results[awaiterResult]
        }

        assertTrue(results[0] > 0, results.toList().toString())
        assertTrue(results[1] > 0, results.toList().toString())
    }
}
