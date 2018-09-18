/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class JobActivationStressTest : TestBase() {
    private val N_ITERATIONS = 10_000 * stressTestMultiplier
    private val pool = newFixedThreadPoolContext(3, "JobActivationStressTest")

    @After
    fun tearDown() {
        pool.close()
    }

    /**
     * Perform concurrent start & cancel of a job with prior installed completion handlers
     */
    @Test
    @Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN")
    fun testActivation() = runTest {
        val barrier = CyclicBarrier(3)
        val scope = CoroutineScope(pool)
        repeat(N_ITERATIONS) {
            var wasStarted = false
            val d = scope.async(start = CoroutineStart.LAZY) {
                wasStarted = true
                throw TestException()
            }
            // need to add on completion handler
            val causeHolder = object {
                var cause: Throwable? = null
            }
            // we use synchronization on causeHolder to work around the fact that completion listeners
            // are invoked after the job is in the final state, so when "d.join()" completes there is
            // no guarantee that this listener was already invoked
            d.invokeOnCompletion {
                synchronized(causeHolder) {
                    causeHolder.cause = it ?: Error("Empty cause")
                    (causeHolder as Object).notifyAll()
                }
            }
            // concurrent cancel
            val canceller = scope.launch {
                barrier.await()
                d.cancel()
            }
            // concurrent cancel
            val starter = scope.launch {
                barrier.await()
                d.start()
            }
            barrier.await()
            joinAll(d, canceller, starter)
            if (wasStarted) {
                val exception = d.getCompletionExceptionOrNull()
                assertTrue(exception is TestException, "exception=$exception")
                val cause = synchronized(causeHolder) {
                    while (causeHolder.cause == null) (causeHolder as Object).wait()
                    causeHolder.cause
                }
                assertTrue(cause is TestException, "cause=$cause")
            }
        }
    }

    private class TestException : Exception()
}