/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlin.test.*

class AsyncTest : TestBase() {

    @Test
    fun testSimple() = runTest {
        expect(1)
        val d = async(coroutineContext) {
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
        val d = async(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
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
        val d = async(coroutineContext) {
            finish(3)
            throw TestException()
        }
        expect(2)
        d.await() // will throw TestException
    }

    @Test
    fun testCancellationWithCause() = runTest(expected = { it is AssertionError }) {
        expect(1)
        val d = async(coroutineContext, CoroutineStart.ATOMIC) {
            finish(3)
            yield()
        }

        expect(2)
        d.cancel(AssertionError())
        d.await()
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
        val deferred = async(Job()) {
            val decomposed = async {
                throw AssertionError()
                1
            }

            try {
                decomposed.await()
            } catch (e: AssertionError) {
                42
            }
        }

        assertEquals(42, deferred.await())
    }


    @Test
    fun testParallelDecompositionCaughtExceptionWithInheritedParent() = runTest {
        val deferred = async(coroutineContext) {
            val decomposed = async(coroutineContext) {
                throw AssertionError()
                1
            }

            try {
                decomposed.await()
            } catch (e: AssertionError) {
                42
            }
        }

        assertEquals(42, deferred.await())
    }

    @Test
    fun testParallelDecompositionUncaughtExceptionWithInheritedParent() = runTest(expected = { it is AssertionError }) {
        val deferred = async(coroutineContext) {
            val decomposed = async(coroutineContext) {
                throw AssertionError()
                1
            }

            decomposed.await()
        }

        deferred.await()
        expectUnreached()
    }

    @Test
    fun testParallelDecompositionUncaughtException() = runTest(expected = { it is AssertionError }) {
        val deferred = async(Job()) {
            val decomposed = async {
                throw AssertionError()
                1
            }

            decomposed.await()
        }

        deferred.await()
        expectUnreached()
    }

    @Test
    fun testCancellationTransparency() = runTest {
        val deferred = async(kotlin.coroutines.experimental.coroutineContext, CoroutineStart.ATOMIC) {
            expect(2)
            throw TestException()
        }

        expect(1)
        deferred.cancel(UnsupportedOperationException())

        try {
            deferred.await()
        } catch (e: UnsupportedOperationException) {
            finish(3)
        }
    }

    @Test
    fun testDeferAndYieldException() = runTest(expected = { it is TestException }) {
        expect(1)
        val d = async(coroutineContext) {
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
        val d = async(coroutineContext) {
            expect(5)
            yield()
            expect(9)
            42
        }
        expect(2)
        launch(coroutineContext) {
            expect(6)
            assertEquals(d.await(), 42)
            expect(11)
        }
        expect(3)
        launch(coroutineContext) {
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

    class BadClass {
        override fun equals(other: Any?): Boolean = error("equals")
        override fun hashCode(): Int = error("hashCode")
        override fun toString(): String = error("toString")
    }

    @Test
    fun testDeferBadClass() = runTest {
        val bad = BadClass()
        val d = async(coroutineContext) {
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
        } catch (e: JobCancellationException) {
            finish(3)
        }
    }

    private class TestException : Exception()
}
