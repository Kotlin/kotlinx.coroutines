package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.ThreadFactory
import java.util.concurrent.atomic.AtomicInteger
import kotlin.coroutines.CoroutineContext

class WithTimeoutThreadDispatchTest : TestBase() {
    var executor: ExecutorService? = null

    @AfterTest
    fun tearDown() {
        executor?.shutdown()
    }

    @Test
    fun testCancellationDispatchScheduled() {
        checkCancellationDispatch {
            executor = Executors.newScheduledThreadPool(1, it)
            executor!!.asCoroutineDispatcher()
        }
    }

    @Test
    fun testCancellationDispatchNonScheduled() {
        checkCancellationDispatch {
            executor = Executors.newSingleThreadExecutor(it)
            executor!!.asCoroutineDispatcher()
        }
    }

    @Test
    fun testCancellationDispatchCustomNoDelay() {
        // it also checks that there is at most once scheduled request in flight (no spurious concurrency)
        var error: String? = null
        checkCancellationDispatch {
            executor = Executors.newSingleThreadExecutor(it)
            val scheduled = AtomicInteger(0)
            object : CoroutineDispatcher() {
                override fun dispatch(context: CoroutineContext, block: Runnable) {
                    if (scheduled.incrementAndGet() > 1) error = "Two requests are scheduled concurrently"
                    executor!!.execute {
                        scheduled.decrementAndGet()
                        block.run()
                    }
                }
            }
        }
        error?.let { error(it) }
    }

    private fun checkCancellationDispatch(factory: (ThreadFactory) -> CoroutineDispatcher) = runBlocking {
        expect(1)
        var thread: Thread? = null
        val dispatcher = factory(ThreadFactory { Thread(it).also { thread = it } })
        withContext(dispatcher) {
            expect(2)
            assertEquals(thread, Thread.currentThread())
            try {
                withTimeout(100) {
                    try {
                        expect(3)
                        delay(1000)
                        expectUnreached()
                    } catch (e: CancellationException) {
                        expect(4)
                        assertEquals(thread, Thread.currentThread())
                        throw e // rethrow
                    }
                }
            } catch (e: CancellationException) {
                expect(5)
                assertEquals(thread, Thread.currentThread())
            }
            expect(6)
        }
        finish(7)
    }
}