package kotlinx.coroutines.future

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import java.io.*
import java.util.concurrent.*
import kotlin.test.*

class FutureExceptionsTest : TestBase() {

    @Test
    fun testConsume() {
        testException(IOException(), { it is IOException })
    }

    @Test
    fun testConsumeChained() {
        testException(IOException(), { it is IOException }, { f -> f.thenApply { it + 1 } })
    }

    @Test
    fun testConsumeDeepChain() {
        testException(IOException(), { it is IOException },
            { f -> f
                .thenApply { it + 1 }
                .thenApply { it + 2 } })
    }

    @Test
    fun testConsumeCompletionException() {
        testException(CompletionException("test", IOException()), { it is IOException })
    }

    @Test
    fun testConsumeChainedCompletionException() {
        testException(CompletionException("test", IOException()), { it is IOException }, { f -> f.thenApply { it + 1 } })
    }

    @Test
    fun testConsumeTestException() {
        testException(TestException(), { it is TestException })
    }

    @Test
    fun testConsumeChainedTestException() {
        testException(TestException(), { it is TestException }, { f -> f.thenApply { it + 1 } })
    }

    private fun testException(
        exception: Throwable,
        expected: ((Throwable) -> Boolean),
        transformer: (CompletableFuture<Int>) -> CompletableFuture<Int> = { it }
    ) {

        // Fast path
        runTest {
            val future = CompletableFuture<Int>()
            val chained = transformer(future)
            future.completeExceptionally(exception)
            try {
                chained.consume()
            } catch (e: Throwable) {
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
                chained.consume()
            } catch (e: Throwable) {
                assertTrue(expected(e))
            }
        }
    }
}
