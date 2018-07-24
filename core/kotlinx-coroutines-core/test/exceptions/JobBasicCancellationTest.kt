package kotlinx.coroutines.experimental.exceptions

import kotlinx.coroutines.experimental.*
import org.junit.Test
import java.io.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

/*
 * Basic checks that check that cancellation more or less works,
 * parent is not cancelled on child cancellation and launch {}, Job(), async {} and
 * CompletableDeferred are indistinguishable
 */
class JobBasicCancellationTest : TestBase() {

    @Test
    fun testJobCancelChild() = runTest {
        val parent = launch(coroutineContext) {
            expect(1)
            val child = launch(coroutineContext) {
                expect(2)
            }

            yield()
            expect(3)
            assertFalse(child.cancel())
            child.join()
            expect(4)
        }

        parent.join()
        finish(5)
    }

    @Test
    fun testJobCancelChildAtomic() = runTest {
        val parent = launch(coroutineContext) {
            expect(1)
            val child = launch(coroutineContext, CoroutineStart.ATOMIC) {
                expect(3)
            }

            expect(2)
            assertTrue(child.cancel())
            try {
                child.join()
            } catch (e: Exception) {
                throw e
            }
            expect(4)
        }

        parent.join()
        finish(5)
    }

    @Test
    fun testAsyncCancelChild() = runTest {
        val parent = async(coroutineContext) {
            expect(1)
            val child = async(coroutineContext) {
                expect(2)
            }

            yield()
            expect(3)
            assertFalse(child.cancel())
            child.await()
            expect(4)
        }

        parent.await()
        finish(5)
    }

    @Test
    fun testAsyncCancelChildAtomic() = runTest {
        val parent = async(coroutineContext) {
            expect(1)
            val child = async(coroutineContext, CoroutineStart.ATOMIC) {
                expect(3)
            }

            expect(2)
            assertTrue(child.cancel())
            child.join()
            expect(4)
        }

        parent.await()
        finish(5)
    }

    @Test
    fun testCancelJobImpl() = runTest {
        val parent = launch(coroutineContext) {
            expect(1)
            val child = Job(coroutineContext[Job])
            expect(2)
            assertFalse(child.cancel(IOException()))
            child.join()
            assertTrue(child.getCancellationException().cause is IOException)
            expect(3)
        }

        parent.join()
        finish(4)
    }

    @Test
    fun cancelCompletableDeferred() = runTest {
        val parent = launch(coroutineContext) {
            expect(1)
            val child = CompletableDeferred<Unit>(coroutineContext[Job])
            expect(2)
            assertTrue(child.cancel(IOException()))
            child.join()
            assertTrue(child.getCancellationException().cause is IOException)
            expect(3)
        }

        parent.join()
        finish(4)
    }

    @Test
    fun testConsecutiveCancellation() {
        val deferred = CompletableDeferred<Int>()
        assertTrue(deferred.completeExceptionally(IndexOutOfBoundsException()))
        assertFalse(deferred.completeExceptionally(AssertionError()))
        val cause = deferred.getCancellationException().cause!!
        assertTrue(cause is IndexOutOfBoundsException)
        assertNull(cause.cause)
        assertTrue(cause.suppressed().isEmpty())
    }
}
