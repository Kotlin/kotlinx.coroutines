package kotlinx.coroutines

import kotlinx.coroutines.testing.TestBase
import java.lang.ref.WeakReference
import kotlin.coroutines.AbstractCoroutineContextElement
import kotlin.coroutines.Continuation
import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.CoroutineContext
import kotlin.test.Test
import kotlin.test.assertNull

/*
 * This is an adapted verion of test from #4296.
 *
 * qwwdfsad: the test relies on System.gc() actually collecting the garbage.
 * If these tests flake on CI, first check that JDK/GC setup in not an issue.
 */
class ThreadLocalCustomContinuationInterceptorTest : TestBase() {

    private class CustomContinuationInterceptor(private val delegate: ContinuationInterceptor) :
        AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {

        override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> {
            return delegate.interceptContinuation(continuation)
        }
    }

    private class CustomNeverEqualContinuationInterceptor(private val delegate: ContinuationInterceptor) :
        AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {

        override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> {
            return delegate.interceptContinuation(continuation)
        }

        override fun equals(other: Any?) = false
    }

    @Test
    fun testDefaultDispatcherNoSuspension() = ensureCoroutineContextGCed(Dispatchers.Default, suspend = false)

    @Test
    fun testDefaultDispatcher() = ensureCoroutineContextGCed(Dispatchers.Default, suspend = true)


    @Test
    fun testNonCoroutineDispatcher() = ensureCoroutineContextGCed(
        CustomContinuationInterceptor(Dispatchers.Default),
        suspend = true
    )

    @Test
    fun testNonCoroutineDispatcherSuspension() = ensureCoroutineContextGCed(
        CustomContinuationInterceptor(Dispatchers.Default),
        suspend = false
    )

    // Note asymmetric equals codepath never goes through the undispatched withContext, thus the separate test case

    @Test
    fun testNonCoroutineDispatcherAsymmetricEquals() =
        ensureCoroutineContextGCed(
            CustomNeverEqualContinuationInterceptor(Dispatchers.Default),
            suspend = true
        )

    @Test
    fun testNonCoroutineDispatcherAsymmetricEqualsSuspension() =
        ensureCoroutineContextGCed(
            CustomNeverEqualContinuationInterceptor(Dispatchers.Default),
            suspend = false
        )


    private fun ensureCoroutineContextGCed(coroutineContext: CoroutineContext, suspend: Boolean) {
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

            // Twice is enough to ensure
            System.gc()
            System.gc()
            assertNull(ref.get())
        }
    }

}
