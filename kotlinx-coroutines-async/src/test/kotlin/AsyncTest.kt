package kotlinx.coroutines

import org.junit.Test
import java.util.concurrent.CompletableFuture
import java.util.concurrent.ExecutionException
import java.util.concurrent.atomic.AtomicInteger
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue
import kotlin.test.fail

class AsyncTest {
    @Test
    fun testSimple() {
        val future = async<String> {
            CompletableFuture.supplyAsync {
                "O"
            }.await() + "K"
        }

        assertEquals("OK", future.get())
    }

    @Test
    fun testWaitForCompletion() {
        val toAwait = CompletableFuture<String>()
        val future = async<String> {
            toAwait.await() + "K"
        }

        assertFalse(future.isDone)
        toAwait.complete("O")

        assertEquals("OK", future.get())
    }

    @Test
    fun testAwaitedFutureCompletedExceptionally() {
        val toAwait = CompletableFuture<String>()
        val future = async<String> {
            try {
                toAwait.await()
            } catch (e: RuntimeException) {
                e.message!!
            } + "K"
        }

        assertFalse(future.isDone)
        toAwait.completeExceptionally(RuntimeException("O"))

        assertEquals("OK", future.get())
    }

    @Test
    fun testExceptionInsideCoroutine() {
        val future = async<String> {
            if (CompletableFuture.supplyAsync { true }.await()) {
                throw IllegalStateException("OK")
            }
            CompletableFuture.supplyAsync { "fail" }.await()
        }

        try {
            future.get()
            fail("'get' should've throw an exception")
        } catch (e: ExecutionException) {
            assertTrue(e.cause is IllegalStateException)
            assertEquals("OK", e.cause!!.message)
        }
    }

    @Test
    fun testContinuationWrapped() {
        val depth = AtomicInteger()

        val future = async<String>(continuationWrapper = {
            depth.andIncrement
            it()
            depth.andDecrement
        }) {
            assertEquals(1, depth.get(), "Part before first suspension must be wrapped")

            val result =
                    CompletableFuture.supplyAsync {
                        while (depth.get() > 0);

                        assertEquals(0, depth.get(), "Part inside suspension point should not be wrapped")
                        "OK"
                    }.await()

            assertEquals(1, depth.get(), "Part after first suspension should be wrapped")

            CompletableFuture.supplyAsync {
                while (depth.get() > 0);

                assertEquals(0, depth.get(), "Part inside suspension point should not be wrapped")
                "ignored"
            }.await()

            result
        }

        assertEquals("OK", future.get())
    }
}
