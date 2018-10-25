/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.guava

import com.google.common.util.concurrent.*
import kotlinx.coroutines.*
import org.junit.Test
import java.io.*
import java.util.concurrent.*
import kotlin.test.*

class ListenableFutureExceptionsTest : TestBase() {

    @Test
    fun testAwait() {
        testException(IOException(), { it is IOException })
    }

    @Test
    fun testAwaitChained() {
        testException(IOException(), { it is IOException }, { i -> i!! + 1 })
    }

    @Test
    fun testAwaitCompletionException() {
        testException(CompletionException("test", IOException()), { it is CompletionException })
    }

    @Test
    fun testAwaitChainedCompletionException() {
        testException(
            CompletionException("test", IOException()),
            { it is CompletionException },
            { i -> i!! + 1 })
    }

    @Test
    fun testAwaitTestException() {
        testException(TestException(), { it is TestException })
    }

    @Test
    fun testAwaitChainedTestException() {
        testException(TestException(), { it is TestException }, { i -> i!! + 1 })
    }

    private fun testException(
        exception: Throwable,
        expected: ((Throwable) -> Boolean),
        transformer: ((Int?) -> Int?)? = null
    ) {

        // Fast path
        runTest {
            val future = SettableFuture.create<Int>()
            val chained = if (transformer == null) future else Futures.transform(future, transformer)
            future.setException(exception)
            try {
                chained.await()
            } catch (e: Throwable) {
                assertTrue(expected(e))
            }
        }

        // Slow path
        runTest {
            val future = SettableFuture.create<Int>()
            val chained = if (transformer == null) future else Futures.transform(future, transformer)
            launch {
                future.setException(exception)
            }

            try {
                chained.await()
            } catch (e: Throwable) {
                assertTrue(expected(e))
            }
        }
    }
}
