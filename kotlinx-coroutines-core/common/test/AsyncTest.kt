/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED", "UNREACHABLE_CODE", "USELESS_IS_CHECK") // KT-21913

package kotlinx.coroutines

import kotlin.test.*

@Suppress("DEPRECATION") // cancel(cause)
class AsyncTest : TestBase() {

    @Test
    fun testSimple() = runTest {
        expect(1)
        val d = async {
            expect(3)
            42
        }
        expect(2)
        assertTrue(d.isActive)
        assertEquals(d.await(), 42)
        assertTrue(!d.isActive)
        expect(4)
        assertEquals(d.await(), 42) // second await -- same result
        finish(5)
    }

    @Test
    fun testUndispatched() = runTest {
        expect(1)
        val d = async(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            42
        }
        expect(3)
        assertTrue(!d.isActive)
        assertEquals(d.await(), 42)
        finish(4)
    }

    @Test
    fun testSimpleException() = runTest(expected = { it is TestException }) {
        expect(1)
        val d = async<Unit> {
            finish(3)
            throw TestException()
        }
        expect(2)
        d.await() // will throw TestException
    }

    @Test
    fun testCancellationWithCause() = runTest {
        expect(1)
        val d = async(NonCancellable, start = CoroutineStart.ATOMIC) {
            expect(3)
            yield()
        }
        expect(2)
        d.cancel(TestCancellationException("TEST"))
        try {
            d.await()
        } catch (e: TestCancellationException) {
            finish(4)
            assertEquals("TEST", e.message)
        }
    }

    @Test
    fun testLostException() = runTest {
        expect(1)
        val deferred = async(Job()) {
            expect(2)
            throw Exception()
        }

        // Exception is not consumed -> nothing is reported
        deferred.join()
        finish(3)
    }

    @Test
    fun testParallelDecompositionCaughtException() = runTest {
        val deferred = async(NonCancellable) {
            val decomposed = async(NonCancellable) {
                throw TestException()
                1
            }
            try {
                decomposed.await()
            } catch (e: TestException) {
                42
            }
        }
        assertEquals(42, deferred.await())
    }

    @Test
    fun testParallelDecompositionCaughtExceptionWithInheritedParent() = runTest {
        expect(1)
        val deferred = async(NonCancellable) {
            expect(2)
            val decomposed = async { // inherits parent job!
                expect(3)
                throw TestException()
                1
            }
            try {
                decomposed.await()
            } catch (e: TestException) {
                expect(4) // Should catch this exception, but parent is already cancelled
                42
            }
        }
        try {
            // This will fail
            assertEquals(42, deferred.await())
        } catch (e: TestException) {
            finish(5)
        }
    }

    @Test
    fun testParallelDecompositionUncaughtExceptionWithInheritedParent() = runTest(expected = { it is TestException }) {
        val deferred = async(NonCancellable) {
            val decomposed = async {
                throw TestException()
                1
            }

            decomposed.await()
        }

        deferred.await()
        expectUnreached()
    }

    @Test
    fun testParallelDecompositionUncaughtException() = runTest(expected = { it is TestException }) {
        val deferred = async(NonCancellable) {
            val decomposed = async {
                throw TestException()
                1
            }

            decomposed.await()
        }

        deferred.await()
        expectUnreached()
    }

    @Test
    fun testCancellationTransparency() = runTest {
        val deferred = async(NonCancellable, start = CoroutineStart.ATOMIC) {
            expect(2)
            throw TestException()
        }
        expect(1)
        deferred.cancel()
        try {
            deferred.await()
        } catch (e: TestException) {
            finish(3)
        }
    }

    @Test
    fun testDeferAndYieldException() = runTest(expected = { it is TestException }) {
        expect(1)
        val d = async<Unit> {
            expect(3)
            yield() // no effect, parent waiting
            finish(4)
            throw TestException()
        }
        expect(2)
        d.await() // will throw IOException
    }

    @Test
    fun testDeferWithTwoWaiters() = runTest {
        expect(1)
        val d = async {
            expect(5)
            yield()
            expect(9)
            42
        }
        expect(2)
        launch {
            expect(6)
            assertEquals(d.await(), 42)
            expect(11)
        }
        expect(3)
        launch {
            expect(7)
            assertEquals(d.await(), 42)
            expect(12)
        }
        expect(4)
        yield() // this actually yields control to async, which produces results and resumes both waiters (in order)
        expect(8)
        yield() // yield again to "d", which completes
        expect(10)
        yield() // yield to both waiters
        finish(13)
    }

    @Test
    fun testDeferBadClass() = runTest {
        val bad = BadClass()
        val d = async {
            expect(1)
            bad
        }
        assertSame(d.await(), bad)
        finish(2)
    }

    @Test
    fun testOverriddenParent() = runTest {
        val parent = Job()
        val deferred = async(parent, CoroutineStart.ATOMIC) {
            expect(2)
            delay(Long.MAX_VALUE)
        }

        parent.cancel()
        try {
            expect(1)
            deferred.await()
        } catch (e: CancellationException) {
            finish(3)
        }
    }

    @Test
    fun testIncompleteAsyncState() = runTest {
        val deferred = async {
            coroutineContext[Job]!!.invokeOnCompletion {  }
        }

        deferred.await().dispose()
        assertTrue(deferred.getCompleted() is DisposableHandle)
        assertNull(deferred.getCompletionExceptionOrNull())
        assertTrue(deferred.isCompleted)
        assertFalse(deferred.isActive)
        assertFalse(deferred.isCancelled)
    }

    @Test
    fun testIncompleteAsyncFastPath() = runTest {
        val deferred = async(Dispatchers.Unconfined) {
            coroutineContext[Job]!!.invokeOnCompletion {  }
        }

        deferred.await().dispose()
        assertTrue(deferred.getCompleted() is DisposableHandle)
        assertNull(deferred.getCompletionExceptionOrNull())
        assertTrue(deferred.isCompleted)
        assertFalse(deferred.isActive)
        assertFalse(deferred.isCancelled)
    }

    @Test
    fun testAsyncWithFinally() = runTest {
        expect(1)

        @Suppress("UNREACHABLE_CODE")
        val d = async {
            expect(3)
            try {
                yield() // to main, will cancel
            } finally {
                expect(6) // will go there on await
                return@async "Fail" // result will not override cancellation
            }
            expectUnreached()
            "Fail2"
        }
        expect(2)
        yield() // to async
        expect(4)
        check(d.isActive && !d.isCompleted && !d.isCancelled)
        d.cancel()
        check(!d.isActive && !d.isCompleted && d.isCancelled)
        check(!d.isActive && !d.isCompleted && d.isCancelled)
        expect(5)
        try {
            d.await() // awaits
            expectUnreached() // does not complete normally
        } catch (e: Throwable) {
            expect(7)
            check(e is CancellationException)
        }
        check(!d.isActive && d.isCompleted && d.isCancelled)
        finish(8)
    }
}
