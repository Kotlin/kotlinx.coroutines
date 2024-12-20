package kotlinx.coroutines

import kotlinx.coroutines.testing.TestBase
import kotlinx.coroutines.testing.isJavaAndWindows
import java.lang.ref.WeakReference
import kotlin.coroutines.AbstractCoroutineContextElement
import kotlin.coroutines.Continuation
import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.CoroutineContext
import kotlin.test.*

/*
 * This is an adapted verion of test from #4296.
 *
 * qwwdfsad: the test relies on System.gc() actually collecting the garbage.
 * If these tests flake on CI, first check that JDK/GC setup in not an issue.
 */
@Ignore
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

    @Test(timeout = 20_000L)
    fun testDefaultDispatcherNoSuspension() = ensureCoroutineContextGCed(Dispatchers.Default, suspend = false)

    @Test(timeout = 20_000L)
    fun testDefaultDispatcher() = ensureCoroutineContextGCed(Dispatchers.Default, suspend = true)

    @Test(timeout = 20_000L)
    fun testNonCoroutineDispatcher() = ensureCoroutineContextGCed(
        CustomContinuationInterceptor(Dispatchers.Default),
        suspend = true
    )

    @Test(timeout = 20_000L)
    fun testNonCoroutineDispatcherSuspension() = ensureCoroutineContextGCed(
        CustomContinuationInterceptor(Dispatchers.Default),
        suspend = false
    )

    // Note asymmetric equals codepath never goes through the undispatched withContext, thus the separate test case

    @Test(timeout = 20_000L)
    fun testNonCoroutineDispatcherAsymmetricEquals() =
        ensureCoroutineContextGCed(
            CustomNeverEqualContinuationInterceptor(Dispatchers.Default),
            suspend = true
        )

    @Test(timeout = 20_000L)
    fun testNonCoroutineDispatcherAsymmetricEqualsSuspension() =
        ensureCoroutineContextGCed(
            CustomNeverEqualContinuationInterceptor(Dispatchers.Default),
            suspend = false
        )


    @Volatile
    private var letThatSinkIn: Any = "What is my purpose? To frag the garbage collctor"

    private fun ensureCoroutineContextGCed(coroutineContext: CoroutineContext, suspend: Boolean) {
        // Tests are pretty timing-sensitive and flake ehavily on our virtualized Windows environment
        if (isJavaAndWindows) {
            return
        }

        fun forceGcUntilRefIsCleaned(ref: WeakReference<CoroutineName>) {
            while (ref.get() != null) {
                System.gc()
                letThatSinkIn = LongArray(1024 * 1024)
            }
        }

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

            forceGcUntilRefIsCleaned(ref)
        }
    }
}
