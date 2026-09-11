package kotlinx.coroutines.guava

import kotlinx.coroutines.testing.*
import com.google.common.base.*
import com.google.common.util.concurrent.*
import kotlinx.coroutines.*
import org.junit.Test
import java.io.*
import java.util.concurrent.*
import kotlin.test.*

class ListenableFutureExceptionsTest : TestBase() {

    @Test
    fun testConsume() {
        testException(IOException(), { it is IOException })
    }

    @Test
    fun testConsumeChained() {
        testException(IOException(), { it is IOException }, { i -> i!! + 1 })
    }

    @Test
    fun testConsumeCompletionException() {
        testException(CompletionException("test", IOException()), { it is CompletionException })
    }

    @Test
    fun testConsumeChainedCompletionException() {
        testException(
            CompletionException("test", IOException()),
            { it is CompletionException },
            { i -> i!! + 1 })
    }

    @Test
    fun testConsumeTestException() {
        testException(TestException(), { it is TestException })
    }

    @Test
    fun testConsumeChainedTestException() {
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
            val chained = if (transformer == null) {
                future
            } else {
                Futures.transform(future, Function(transformer), MoreExecutors.directExecutor())
            }
            future.setException(exception)
            try {
                chained.consume()
            } catch (e: Throwable) {
                assertTrue(expected(e))
            }
        }

        // Slow path
        runTest {
            val future = SettableFuture.create<Int>()
            val chained = if (transformer == null) {
                future
            } else {
                Futures.transform(future, Function(transformer), MoreExecutors.directExecutor())
            }
            launch {
                future.setException(exception)
            }

            try {
                chained.consume()
            } catch (e: Throwable) {
                assertTrue(expected(e))
            }
        }
    }
}
