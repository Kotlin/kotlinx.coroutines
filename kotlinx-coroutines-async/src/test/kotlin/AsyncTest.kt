package kotlinx.coroutines.async

import kotlinx.coroutines.async
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
            await(CompletableFuture.supplyAsync {
                "O"
            }) + "K"
        }

        assertEquals("OK", future.get())
    }

    @Test
    fun testWaitForCompletion() {
        val toAwait = CompletableFuture<String>()
        val future = async<String> {
            await(toAwait) + "K"
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
                await(toAwait)
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
            if (await(CompletableFuture.supplyAsync { true })) {
                throw IllegalStateException("OK")
            }
            await(CompletableFuture.supplyAsync { "fail" })
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
            assertEquals(0, depth.get(), "Part before first suspension should not be wrapped")

            val result =
                    await(CompletableFuture.supplyAsync {
                        while (depth.get() > 0);

                        assertEquals(0, depth.get(), "Part inside suspension point should not be wrapped")
                        "OK"
                    })

            assertEquals(1, depth.get(), "Part after first suspension should be wrapped")

            await(CompletableFuture.supplyAsync {
                while (depth.get() > 0);

                assertEquals(0, depth.get(), "Part inside suspension point should not be wrapped")
                "ignored"
            })

            result
        }

        assertEquals("OK", future.get())
    }
}
