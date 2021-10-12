/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.Test
import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

class LimitedParallelismTest : TestBase() {

    @Test
    fun testParallelismSpec() {
        assertFailsWith<IllegalArgumentException> { Dispatchers.Default.limitedParallelism(0) }
        assertFailsWith<IllegalArgumentException> { Dispatchers.Default.limitedParallelism(-1) }
        assertFailsWith<IllegalArgumentException> { Dispatchers.Default.limitedParallelism(Int.MIN_VALUE) }
        Dispatchers.Default.limitedParallelism(Int.MAX_VALUE)
    }

    @Test
    fun testTaskFairness() = runTest {
        val executor = newSingleThreadContext("test")
        val view = executor.limitedParallelism(1)
        val view2 = executor.limitedParallelism(1)
        val j1 = launch(view) {
            while (true) {
                yield()
            }
        }
        val j2 = launch(view2) { j1.cancel() }
        joinAll(j1, j2)
        executor.close()
    }

    @Test
    fun testUnhandledException() = runTest {
        var caughtException: Throwable? = null
        val executor = Executors.newFixedThreadPool(
            1
        ) {
            Thread(it).also {
                it.uncaughtExceptionHandler = Thread.UncaughtExceptionHandler { _, e -> caughtException = e }
            }
        }.asCoroutineDispatcher()
        val view = executor.limitedParallelism(1)
        view.dispatch(EmptyCoroutineContext, Runnable { throw TestException() })
        withContext(view) {
            // Verify it is in working state and establish happens-before
        }
        assertTrue { caughtException is TestException }
        executor.close()
    }
}
