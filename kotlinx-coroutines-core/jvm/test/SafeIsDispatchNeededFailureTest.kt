package kotlinx.coroutines

import kotlin.test.Test
import kotlin.test.assertTrue
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlinx.coroutines.internal.*

class SafeIsDispatchNeededFailureTest {
    @Test
    fun testSafeIsDispatchNeededThrowsDispatchException() {
        val dispatcher = object : CoroutineDispatcher() {
            override fun isDispatchNeeded(context: CoroutineContext): Boolean {
                throw RuntimeException("isDispatchNeeded boom")
            }

            override fun dispatch(context: CoroutineContext, block: Runnable) {
                // no-op
            }
        }

        var thrown: Throwable? = null
        try {
            dispatcher.safeIsDispatchNeeded(EmptyCoroutineContext)
        } catch (e: Throwable) {
            thrown = e
        }

        assertTrue(thrown is DispatchException, "safeIsDispatchNeeded should throw DispatchException, got: $thrown")
        assertTrue(thrown?.cause is RuntimeException, "cause should be original RuntimeException")
    }
}
                                // no-op
