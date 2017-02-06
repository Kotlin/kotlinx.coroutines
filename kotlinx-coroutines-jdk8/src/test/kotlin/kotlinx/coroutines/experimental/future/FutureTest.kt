package kotlinx.coroutines.experimental.future

import kotlinx.coroutines.experimental.CoroutineDispatcher
import org.junit.Test
import java.util.concurrent.CompletableFuture
import java.util.concurrent.ExecutionException
import java.util.concurrent.atomic.AtomicInteger
import kotlin.coroutines.experimental.CoroutineContext
import org.junit.Assert.*

class FutureTest {
    @Test
    fun testSimple() {
        val future = future {
            CompletableFuture.supplyAsync {
                "O"
            }.await() + "K"
        }

        assertEquals("OK", future.get())
    }

    @Test
    fun testWaitForCompletion() {
        val toAwait = CompletableFuture<String>()
        val future = future {
            toAwait.await() + "K"
        }

        assertFalse(future.isDone)
        toAwait.complete("O")

        assertEquals("OK", future.get())
    }

    @Test
    fun testDoneFutureCompletedExceptionally() {
        val toAwait = CompletableFuture<String>()
        toAwait.completeExceptionally(RuntimeException("O"))
        val future = future<String> {
            try {
                toAwait.await()
            } catch (e: RuntimeException) {
                e.message!!
            } + "K"
        }

        assertFalse(future.isDone)
        assertEquals("OK", future.get())
    }

    @Test
    fun testAwaitedFutureCompletedExceptionally() {
        val toAwait = CompletableFuture<String>()
        val future = future<String> {
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
        val future = future {
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

        val future = future(wrapContinuation {
            depth.andIncrement
            it()
            depth.andDecrement
        }) {
            assertEquals("Part before first suspension must be wrapped", 1, depth.get())

            val result =
                    CompletableFuture.supplyAsync {
                        while (depth.get() > 0) ;
                        assertEquals("Part inside suspension point should not be wrapped", 0, depth.get())
                        "OK"
                    }.await()

            assertEquals("Part after first suspension should be wrapped", 1, depth.get())

            CompletableFuture.supplyAsync {
                while (depth.get() > 0) ;
                assertEquals("Part inside suspension point should not be wrapped", 0, depth.get())
                "ignored"
            }.await()

            result
        }

        assertEquals("OK", future.get())
    }

    private fun wrapContinuation(wrapper: (() -> Unit) -> Unit): CoroutineDispatcher = object : CoroutineDispatcher() {
        override fun dispatch(context: CoroutineContext, block: Runnable) {
            wrapper {
                block.run()
            }
        }
    }
}
