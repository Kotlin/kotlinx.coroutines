/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.future

import kotlinx.coroutines.experimental.*
import org.junit.Test
import java.io.*
import java.util.concurrent.*
import kotlin.test.*

class FutureExceptionsTest : TestBase() {

    @Test
    fun testAwait() {
        testException(IOException(), { it is IOException })
    }

    @Test
    fun testAwaitChained() {
        testException(IOException(), { it is IOException }, { f -> f.thenApply { it + 1 } })
    }

    @Test
    fun testAwaitDeepChain() {
        testException(IOException(), { it is IOException },
            { f -> f
                .thenApply { it + 1 }
                .thenApply { it + 2 } })
    }

    @Test
    fun testAwaitCompletionException() {
        testException(CompletionException("test", IOException()), { it is IOException })
    }

    @Test
    fun testAwaitChainedCompletionException() {
        testException(CompletionException("test", IOException()), { it is IOException }, { f -> f.thenApply { it + 1 } })
    }

    @Test
    fun testAwaitTestException() {
        testException(TestException(), { it is TestException })
    }

    @Test
    fun testAwaitChainedTestException() {
        testException(TestException(), { it is TestException }, { f -> f.thenApply { it + 1 } })
    }

    class TestException : CompletionException("test2")

    private fun testException(
        exception: Exception,
        expected: ((Throwable) -> Boolean),
        transformer: (CompletableFuture<Int>) -> CompletableFuture<Int> = { it }
    ) {

        // Fast path
        runTest {
            val future = CompletableFuture<Int>()
            val chained = transformer(future)
            future.completeExceptionally(exception)
            try {
                chained.await()
            } catch (e: Exception) {
                assertTrue(expected(e))
            }
        }

        // Slow path
        runTest {
            val future = CompletableFuture<Int>()
            val chained = transformer(future)

            launch {
                future.completeExceptionally(exception)
            }

            try {
                chained.await()
            } catch (e: Exception) {
                assertTrue(expected(e))
            }
        }
    }
}
