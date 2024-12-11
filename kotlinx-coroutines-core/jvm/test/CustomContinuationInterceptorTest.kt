package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.Test
import java.lang.ref.*
import kotlin.coroutines.*
import kotlin.test.*

class CustomContinuationInterceptorTest : TestBase() {

    @Test
    fun `CoroutineDispatcher does not leak CoroutineContext`() =
        ensureCoroutineContextGCed(Dispatchers.Default)

    @Test
    fun `custom ContinuationInterceptor leaks CoroutineContext`() =
        ensureCoroutineContextGCed(CustomContinuationInterceptor(Dispatchers.Default))

    fun ensureCoroutineContextGCed(interceptor: ContinuationInterceptor) = runTest {
        lateinit var ref: WeakReference<CoroutineName>
        val job = GlobalScope.launch(interceptor) {
            val coroutineName = CoroutineName("Yo")
            ref = WeakReference(coroutineName)
            withContext(coroutineName) {
            }
        }
        job.join()

        System.gc()
        assertNull(ref.get())
    }
}

class CustomContinuationInterceptor(private val delegate: ContinuationInterceptor) :
    AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {

    override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> {
        return delegate.interceptContinuation(continuation)
    }
}