package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

class UnconfinedCancellationTest : TestBase() {
    @Test
    fun testUnconfinedCancellation() = runTest {
        launch {
            expect(1)
            cancel()
            launch(Dispatchers.Unconfined) {
                expectUnreached()
            }
        }.join()
        finish(2)
    }

    @Test
    fun testUnconfinedCancellationState() = runTest {
        launch {
            expect(1)
            cancel()
            val job = launch(Dispatchers.Unconfined) {
                expectUnreached()
            }

            assertTrue(job.isCancelled)
            assertTrue(job.isCompleted)
            assertFalse(job.isActive)
        }.join()
        finish(2)
    }

    @Test
    fun testUnconfinedCancellationLazy() = runTest {
        launch {
            expect(1)
            val job = launch(Dispatchers.Unconfined, start = CoroutineStart.LAZY) {
                expectUnreached()
            }
            job.invokeOnCompletion { expect(2) }
            assertFalse(job.isCompleted)
            cancel()
        }.join()
        finish(3)
    }

    @Test
    fun testUndispatchedCancellation() = runTest {
        launch {
            expect(1)
            cancel()
            launch(start = CoroutineStart.UNDISPATCHED) {
                expect(2)
                yield()
                expectUnreached()
            }

        }.join()
        finish(3)
    }

    @Test
    fun testCancelledAtomicUnconfined() = runTest {
        launch {
            expect(1)
            cancel()
            launch(Dispatchers.Unconfined, start = CoroutineStart.ATOMIC) {
                expect(2)
                yield()
                expectUnreached()
            }
        }.join()
        finish(3)
    }


    @Test
    fun testCancelledWithContextUnconfined() = runTest {
        launch {
            expect(1)
            cancel()
            withContext(Dispatchers.Unconfined) {
                expectUnreached()
            }
        }.join()
        finish(2)
    }
}
