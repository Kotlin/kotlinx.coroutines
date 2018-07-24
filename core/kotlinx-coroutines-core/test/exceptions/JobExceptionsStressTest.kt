/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package exceptions

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.exceptions.*
import org.junit.*
import org.junit.Test
import java.io.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class JobExceptionsStressTest : TestBase() {

    private val executor: ThreadPoolDispatcher by lazy { newFixedThreadPoolContext(5, "JobExceptionsStressTest") }

    @After
    fun tearDown() {
        executor.close()
    }

    @Test
    fun testMultipleChildrenThrows() {
        /*
         * Root parent: launched job
         * Owner: launch 3 children, every of it throws an exception, and then call delay()
         * Result: one of the exceptions with the rest two as suppressed
         */
        repeat(100 * stressTestMultiplier) {
            val exception = runBlock(executor) {
                val barrier = CyclicBarrier(4)
                val job = launch(coroutineContext.minusKey(Job)) {

                    launch(coroutineContext) {
                        barrier.await()
                        throw ArithmeticException()
                    }

                    launch(coroutineContext) {
                        barrier.await()
                        throw IOException()
                    }

                    launch(coroutineContext) {
                        barrier.await()
                        throw IllegalArgumentException()
                    }

                    delay(Long.MAX_VALUE)
                }

                barrier.await()
                job.join()
            }

            val classes = mutableSetOf(
                IllegalArgumentException::class,
                IOException::class, ArithmeticException::class)

            val suppressedExceptions = exception.suppressed().toSet()
            assertTrue(classes.remove(exception::class),
                "Failed to remove ${exception::class} from $suppressedExceptions")

            for (throwable in suppressedExceptions.toSet()) { // defensive copy
                assertTrue(classes.remove(throwable::class),
                    "Failed to remove ${throwable::class} from $suppressedExceptions")
            }

            assertTrue(classes.isEmpty())
        }
    }
}