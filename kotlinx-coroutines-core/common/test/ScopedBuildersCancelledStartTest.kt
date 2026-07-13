package kotlinx.coroutines

import kotlinx.coroutines.testing.TestBase
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.test.Test
import kotlin.test.assertTrue

// See https://github.com/Kotlin/kotlinx.coroutines/issues/4457
class ScopedBuildersCancelledStartTest : TestBase() {

    @Test
    fun testCancelledCoroutineScope() = runTest(expected = { it is CancellationException }) {
        cancel()
        coroutineScope {
            finish(1)
        }
        expectUnreached()
    }

    @Test
    fun testCancelledSupervisorScope() = runTest(expected = { it is CancellationException }) {
        cancel()
        supervisorScope {
            finish(1)
        }
        expectUnreached()
    }

    @Test
    fun testCancelledWithTimeout() = runTest(expected = { it is CancellationException }) {
        cancel()
        withTimeout(Long.MAX_VALUE) {
            finish(1)
        }
        expectUnreached()
    }

    @Test
    fun testWithContext() = runTest(expected = { it is CancellationException }) {
        cancel()
        withContext(EmptyCoroutineContext) {
            assertTrue(coroutineContext.job.isCancelled)
            expect(1)
        }
        finish(2)
    }

    @Test
    fun testWithContextWithDispatcher() = runTest(expected = { it is CancellationException }) {
        cancel()
        withContext(Dispatchers.Unconfined) {
            assertTrue(coroutineContext.job.isCancelled)
            expect(1)
        }
        finish(2)
    }
}
