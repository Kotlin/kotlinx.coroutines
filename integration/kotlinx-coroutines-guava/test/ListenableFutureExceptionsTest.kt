package kotlinx.coroutines.experimental.guava

import com.google.common.util.concurrent.*
import kotlinx.coroutines.experimental.*
import org.junit.Test
import java.io.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*
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

    class TestException : CompletionException("test2")

    private fun testException(
        exception: Exception,
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
            } catch (e: Exception) {
                assertTrue(expected(e))
            }
        }

        // Slow path
        runTest {
            val future = SettableFuture.create<Int>()
            val chained = if (transformer == null) future else Futures.transform(future, transformer)
            launch(coroutineContext) {
                future.setException(exception)
            }

            try {
                chained.await()
            } catch (e: Exception) {
                assertTrue(expected(e))
            }
        }
    }
}
