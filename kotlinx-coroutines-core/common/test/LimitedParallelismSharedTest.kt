package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.test.*

class LimitedParallelismSharedTest : TestBase() {

    @Test
    fun testLimitedDefault() = runTest {
        // Test that evaluates the very basic completion of tasks in limited dispatcher
        // for all supported platforms.
        // For more specific and concurrent tests, see 'concurrent' package.
        val view = Dispatchers.Default.limitedParallelism(1)
        val view2 = Dispatchers.Default.limitedParallelism(1)
        val j1 = launch(view) {
            while (true) {
                yield()
            }
        }
        val j2 = launch(view2) { j1.cancel() }
        joinAll(j1, j2)
    }

    @Test
    fun testParallelismSpec() {
        assertFailsWith<IllegalArgumentException> { Dispatchers.Default.limitedParallelism(0) }
        assertFailsWith<IllegalArgumentException> { Dispatchers.Default.limitedParallelism(-1) }
        assertFailsWith<IllegalArgumentException> { Dispatchers.Default.limitedParallelism(Int.MIN_VALUE) }
        Dispatchers.Default.limitedParallelism(Int.MAX_VALUE)
    }

    /**
     * Checks that even if the dispatcher sporadically fails, the limited dispatcher will still allow reaching the
     * target parallelism level.
     */
    @Test
    fun testLimitedParallelismOfOccasionallyFailingDispatcher() {
        val limit = 5
        var doFail = false
        val workerQueue = mutableListOf<Runnable>()
        val limited = object: CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                if (doFail) throw TestException()
                workerQueue.add(block)
            }
        }.limitedParallelism(limit)
        repeat(6 * limit) {
            try {
                limited.dispatch(EmptyCoroutineContext, Runnable { /* do nothing */ })
            } catch (_: DispatchException) {
                // ignore
            }
            doFail = !doFail
        }
        assertEquals(limit, workerQueue.size)
    }
}
