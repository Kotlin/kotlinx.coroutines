package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.testing.TestBase
import kotlinx.coroutines.testing.isJavaAndWindows
import java.lang.ref.WeakReference
import kotlin.coroutines.AbstractCoroutineContextElement
import kotlin.coroutines.Continuation
import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.CoroutineContext
import kotlin.test.*

/*
 * Copy of [ThreadLocalCustomContinuationInterceptorTest].
 */
@Ignore
class ThreadLocalCustomContinuationInterceptorFlowOnTest : TestBase() {

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
    fun testDefaultDispatcherNoSuspension() = ensureFlowOnGCed(Dispatchers.Default, suspend = false)

    @Test(timeout = 20_000L)
    fun testDefaultDispatcher() = ensureFlowOnGCed(Dispatchers.Default, suspend = true)

    @Test(timeout = 20_000L)
    fun testNonCoroutineDispatcher() = ensureFlowOnGCed(
        CustomContinuationInterceptor(Dispatchers.Default),
        suspend = true
    )

    @Test(timeout = 20_000L)
    fun testNonCoroutineDispatcherSuspension() = ensureFlowOnGCed(
        CustomContinuationInterceptor(Dispatchers.Default),
        suspend = false
    )

    // Note asymmetric equals codepath always goes through the channel path in flowOn, thus the separate test case

    @Test(timeout = 20_000L)
    fun testNonCoroutineDispatcherAsymmetricEquals() =
        ensureFlowOnGCed(
            CustomNeverEqualContinuationInterceptor(Dispatchers.Default),
            suspend = true
        )

    @Test(timeout = 20_000L)
    fun testNonCoroutineDispatcherAsymmetricEqualsSuspension() =
        ensureFlowOnGCed(
            CustomNeverEqualContinuationInterceptor(Dispatchers.Default),
            suspend = false
        )


    @Volatile
    private var letThatSinkIn: Any = "What is my purpose? To frag the garbage collctor"

    private fun ensureFlowOnGCed(coroutineContext: CoroutineContext, suspend: Boolean) {
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
                flow<Unit> {
                    if (suspend) {
                        delay(1)
                    }
                }.flowOn(coroutineName).collect()
            }
            job.join()

            forceGcUntilRefIsCleaned(ref)
        }
    }
}
