/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.exceptions

import kotlinx.coroutines.experimental.*
import org.junit.Test
import java.io.*
import kotlin.test.*

/*
 * Basic checks that check that cancellation more or less works,
 * parent is not cancelled on child cancellation and launch {}, Job(), async {} and
 * CompletableDeferred behave properly
 */
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
            assertFalse(child.cancel())
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
            assertTrue(child.cancel())
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
            assertFalse(child.cancel())
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
            assertTrue(child.cancel())
            child.join()
            expect(4)
        }

        parent.await()
        finish(5)
    }

    @Test
    fun testNestedAsyncFailure() = runTest {
        val deferred = async {
            val nested = async {
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
        val parent = launch {
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
