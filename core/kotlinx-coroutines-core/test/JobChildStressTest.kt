/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class JobChildStressTest : TestBase() {
    private val N_ITERATIONS = 10_000 * stressTestMultiplier
    private val pool = newFixedThreadPoolContext(3, "JobChildStressTest")

    @After
    fun tearDown() {
        pool.close()
    }

    /**
     * Perform concurrent launch of a child job & cancellation of the explicit parent job
     */
    @Test
    @Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN")
    fun testChild() = runTest {
        val barrier = CyclicBarrier(3)
        repeat(N_ITERATIONS) {
            var wasLaunched = false
            var unhandledException: Throwable? = null
            val handler = CoroutineExceptionHandler { _, ex ->
                unhandledException = ex
            }
            val scope = CoroutineScope(pool + handler)
            val parent = CompletableDeferred<Unit>()
            // concurrent child launcher
            val launcher = scope.launch {
                barrier.await()
                // A: launch child for a parent job
                launch(parent) {
                    wasLaunched = true
                    throw TestException()
                }
            }
            // concurrent cancel
            val canceller = scope.launch {
                barrier.await()
                // B: cancel parent job of a child
                parent.cancel()
            }
            barrier.await()
            joinAll(launcher, canceller, parent)
            assertNull(unhandledException)
            if (wasLaunched) {
                val exception = parent.getCompletionExceptionOrNull()
                assertTrue(exception is TestException, "exception=$exception")
            }
        }
    }
}