package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

class UnconfinedCancellationTest : TestBase() {
    @Test
    fun testUnconfinedCancellation() = runTest {
        val parent = Job()
        launch(parent) {
            expect(1)
            parent.cancel()
            launch(Dispatchers.Unconfined) {
                expectUnreached()
            }

        }.join()
        finish(2)
    }

    @Test
    fun testUnconfinedCancellationState() = runTest {
        val parent = Job()
        launch(parent) {
            expect(1)
            parent.cancel()
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
        val parent = Job()
        launch(parent) {
            expect(1)
            val job = launch(Dispatchers.Unconfined, start = CoroutineStart.LAZY) {
                expectUnreached()
            }
            job.invokeOnCompletion { expect(2) }
            assertFalse(job.isCompleted)

            parent.cancel()
            job.join()
        }.join()
        finish(3)
    }

    @Test
    fun testUndispatchedCancellation() = runTest {
        val parent = Job()
        launch(parent) {
            expect(1)
            parent.cancel()
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
        val parent = Job()
        launch(parent) {
            expect(1)
            parent.cancel()
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
        val parent = Job()
        launch(parent) {
            expect(1)
            parent.cancel()
            withContext(Dispatchers.Unconfined) {
                expectUnreached()
            }
        }.join()
        finish(2)
    }
}