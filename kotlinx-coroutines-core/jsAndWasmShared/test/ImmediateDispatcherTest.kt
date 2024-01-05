package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*

class ImmediateDispatcherTest : MainDispatcherTestBase.WithRealTimeDelay() {

    /** Tests that [MainCoroutineDispatcher.immediate] doesn't require dispatches from the test context. */
    @Test
    fun testImmediate() = runTest {
        expect(1)
        val job = launch { expect(3) }
        assertFalse(Dispatchers.Main.immediate.isDispatchNeeded(currentCoroutineContext()))
        withContext(Dispatchers.Main.immediate) {
            expect(2)
        }
        job.join()
        finish(4)
    }

    @Test
    fun testMain() = runTest {
        expect(1)
        val job = launch { expect(2) }
        withContext(Dispatchers.Main) {
            expect(3)
        }
        job.join()
        finish(4)
    }

    override fun isMainThread(): Boolean? = null

    override fun scheduleOnMainQueue(block: () -> Unit) {
        Dispatchers.Default.dispatch(EmptyCoroutineContext, Runnable { block() })
    }
}
