package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.*
import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.test.assertEquals

class DelayJvmTest : TestBase() {
    /**
     * Test that delay works properly in contexts with custom [ContinuationInterceptor]
     */
    @Test
    fun testDelayInArbitraryContext() = runBlocking {
        var thread: Thread? = null
        val pool = Executors.newFixedThreadPool(1) { runnable ->
            Thread(runnable).also { thread = it }
        }
        val context = CustomInterceptor(pool)
        val c = async(context) {
            assertEquals(thread, Thread.currentThread())
            delay(100)
            assertEquals(thread, Thread.currentThread())
            42
        }
        assertEquals(42, c.await())
        pool.shutdown()
    }

    @Test
    fun testDelayWithoutDispatcher() = runBlocking(CoroutineName("testNoDispatcher.main")) {
        // launch w/o a specified dispatcher
        val c = async(CoroutineName("testNoDispatcher.inner")) {
            delay(100)
            42
        }
        assertEquals(42, c.await())
    }

    @Test
    fun testNegativeDelay() = runBlocking {
        expect(1)
        val job = async {
            expect(3)
            delay(0)
            expect(4)
        }

        delay(-1)
        expect(2)
        job.await()
        finish(5)
    }

    class CustomInterceptor(val pool: Executor) : AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {
        override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> =
            Wrapper(pool, continuation)
    }

    class Wrapper<T>(val pool: Executor, private val cont: Continuation<T>) : Continuation<T> {
        override val context: CoroutineContext
            get() = cont.context

        override fun resumeWith(result: Result<T>) {
            pool.execute { cont.resumeWith(result) }
        }
    }
}