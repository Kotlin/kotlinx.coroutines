package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.Test
import java.lang.ref.*
import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

class CustomContinuationInterceptorTest : TestBase() {

    fun `CoroutineDispatcher not suspending does not leak CoroutineContext`() =
        ensureCoroutineContextGCed(Dispatchers.Default, suspend = false)

    @Test
    fun `CoroutineDispatcher suspending does not leak CoroutineContext`() =
        ensureCoroutineContextGCed(Dispatchers.Default, suspend = true)

    @Test
    fun `CustomContinuationInterceptor suspending does not leak CoroutineContext`() =
        ensureCoroutineContextGCed(
            CustomContinuationInterceptor(Dispatchers.Default),
            suspend = true
        )

    // This is the one test that fails
    @Test
    fun `CustomContinuationInterceptor not suspending leaks CoroutineContext`() =
        ensureCoroutineContextGCed(
            CustomContinuationInterceptor(Dispatchers.Default),
            suspend = false
        )

    @Test
    fun `CustomContinuationInterceptor not suspending does not leak CoroutineContext when thread locals cleaned up`() {
        val executor = Executors.newSingleThreadExecutor()
        val dispatcher = executor.asCoroutineDispatcher()

        ensureCoroutineContextGCed(
            CustomContinuationInterceptor(dispatcher),
            suspend = false,
            clearLeak = {
                // Ensure that the ThreadLocal instance is GCed.
                System.gc()
                // At this point, the thread local value is still in Thread.threadLocals, it's a
                // stale entry
                val task = executor.submit {
                    val threadLocals = (1..100).map { ThreadLocal<String>() }.toList()
                    // Grow the size of Thread.threadLocals, forcing a call to expungeStaleEntries
                    threadLocals.forEach { it.set("") }
                    // Cleanup the new thread locals
                    threadLocals.forEach { it.remove() }
                }
                task.get()
                // At this point CoroutineContext should be unreachable.
                System.gc()
            }, cleanup = {
                executor.shutdown()
            })
    }

    @Test
    fun `CustomContinuationInterceptor not suspending does not leak CoroutineContext when thread GCed`() {
        val executor = Executors.newSingleThreadExecutor()
        val dispatcher = executor.asCoroutineDispatcher()

        ensureCoroutineContextGCed(
            CustomContinuationInterceptor(dispatcher),
            suspend = false,
            clearLeak = {
                executor.shutdown()
                executor.awaitTermination(30, TimeUnit.SECONDS)
                // At this point CoroutineContext should be unreachable.
                System.gc()
            })
    }

    @Test
    fun `CustomNeverEqualContinuationInterceptor suspending does not leak CoroutineContext`() =
        ensureCoroutineContextGCed(
            CustomNeverEqualContinuationInterceptor(Dispatchers.Default),
            suspend = true
        )

    @Test
    fun `CustomNeverEqualContinuationInterceptor not suspending does not leak CoroutineContext`() =
        ensureCoroutineContextGCed(
            CustomNeverEqualContinuationInterceptor(Dispatchers.Default),
            suspend = false
        )

    private fun ensureCoroutineContextGCed(
        coroutineContext: CoroutineContext,
        suspend: Boolean,
        clearLeak: () -> Unit = {
            System.gc()
            // Run finalizations
            Thread.sleep(100)
            System.gc()
        },
        cleanup: () -> Unit = {}
    ) {
        runTest {
            lateinit var ref: WeakReference<CoroutineName>
            val job = GlobalScope.launch(coroutineContext) {
                val coroutineName = CoroutineName("Yo")
                ref = WeakReference(coroutineName)
                withContext(coroutineName) {
                    if (suspend) {
                        delay(1)
                    }
                }
            }
            job.join()

            clearLeak()
            try {
                assertNull(ref.get())
            } finally {
                cleanup()
            }
        }
    }

}

class CustomContinuationInterceptor(private val delegate: ContinuationInterceptor) :
    AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {

    override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> {
        return delegate.interceptContinuation(continuation)
    }
}

class CustomNeverEqualContinuationInterceptor(private val delegate: ContinuationInterceptor) :
    AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {

    override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> {
        return delegate.interceptContinuation(continuation)
    }

    override fun equals(other: Any?) = false
}