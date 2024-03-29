package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.Test
import java.io.*
import kotlin.test.*

/*
 * Basic checks that check that cancellation more or less works,
 * parent is not cancelled on child cancellation and launch {}, Job(), async {} and
 * CompletableDeferred behave properly
 */

@Suppress("DEPRECATION") // cancel(cause)
class JobBasicCancellationTest : TestBase() {

    @Test
    fun testJobCancelChild() = runTest {
        val parent = launch {
            expect(1)
            val child = launch {
                expect(2)
            }

            yield()
            expect(3)
            child.cancel()
            child.join()
            expect(4)
        }

        parent.join()
        finish(5)
    }

    @Test
    fun testJobCancelChildAtomic() = runTest {
        val parent = launch {
            expect(1)
            val child = launch(start = CoroutineStart.ATOMIC) {
                expect(3)
            }

            expect(2)
            child.cancel()
            child.join()
            yield()
            expect(4)
        }

        parent.join()
        assertTrue(parent.isCompleted)
        assertFalse(parent.isCancelled)
        finish(5)
    }

    @Test
    fun testAsyncCancelChild() = runTest {
        val parent = async {
            expect(1)
            val child = async {
                expect(2)
            }

            yield()
            expect(3)
            child.cancel()
            child.await()
            expect(4)
        }

        parent.await()
        finish(5)
    }

    @Test
    fun testAsyncCancelChildAtomic() = runTest {
        val parent = async {
            expect(1)
            val child = async(start = CoroutineStart.ATOMIC) {
                expect(3)
            }

            expect(2)
            child.cancel()
            child.join()
            expect(4)
        }

        parent.await()
        finish(5)
    }

    @Test
    fun testNestedAsyncFailure() = runTest {
        val deferred = async(NonCancellable) {
            val nested = async(NonCancellable) {
                expect(3)
                throw IOException()
            }

            expect(2)
            yield()
            expect(4)
            nested.await()
        }

        expect(1)
        try {
            deferred.await()
        } catch (e: IOException) {
            finish(5)
        }
    }

    @Test
    fun testCancelJobImpl() = runTest {
        val parent = launch {
            expect(1)
            val child = Job(coroutineContext[Job])
            expect(2)
            child.cancel() // cancel without cause -- should not cancel us (parent)
            child.join()
            expect(3)
        }
        parent.join()
        finish(4)
    }

    @Test
    fun cancelCompletableDeferred() = runTest {
        val parent = launch {
            expect(1)
            val child = CompletableDeferred<Unit>(coroutineContext[Job])
            expect(2)
            child.cancel() // cancel without cause -- should not cancel us (parent)
            child.join()
            expect(3)
        }

        parent.join()
        finish(4)
    }

    @Test
    fun testConsecutiveCancellation() {
        val deferred = CompletableDeferred<Int>()
        assertTrue(deferred.completeExceptionally(IndexOutOfBoundsException()))
        assertFalse(deferred.completeExceptionally(AssertionError())) // second is too late
        val cause = deferred.getCancellationException().cause!!
        assertIs<IndexOutOfBoundsException>(cause)
        assertNull(cause.cause)
        assertTrue(cause.suppressed.isEmpty())
    }
}
