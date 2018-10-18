/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines

import kotlin.test.*

class AsyncLazyTest : TestBase() {

    @Test
    fun testSimple() = runTest {
        expect(1)
        val d = async(start = CoroutineStart.LAZY) {
            expect(3)
            42
        }
        expect(2)
        assertTrue(!d.isActive && !d.isCompleted)
        assertEquals(d.await(), 42)
        assertTrue(!d.isActive && d.isCompleted && !d.isCancelled)
        expect(4)
        assertEquals(d.await(), 42) // second await -- same result
        finish(5)
    }

    @Test
    fun testLazyDeferAndYield() = runTest {
        expect(1)
        val d = async(start = CoroutineStart.LAZY) {
            expect(3)
            yield() // this has not effect, because parent coroutine is waiting
            expect(4)
            42
        }
        expect(2)
        assertTrue(!d.isActive && !d.isCompleted)
        assertEquals(d.await(), 42)
        assertTrue(!d.isActive && d.isCompleted && !d.isCancelled)
        expect(5)
        assertEquals(d.await(), 42) // second await -- same result
        finish(6)
    }

    @Test
    fun testLazyDeferAndYield2() = runTest {
        expect(1)
        val d = async(start = CoroutineStart.LAZY) {
            expect(7)
            42
        }
        expect(2)
        assertTrue(!d.isActive && !d.isCompleted)
        launch { // see how it looks from another coroutine
            expect(4)
            assertTrue(!d.isActive && !d.isCompleted)
            yield() // yield back to main
            expect(6)
            assertTrue(d.isActive && !d.isCompleted) // implicitly started by main's await
            yield() // yield to d
        }
        expect(3)
        assertTrue(!d.isActive && !d.isCompleted)
        yield() // yield to second child (lazy async is not computing yet)
        expect(5)
        assertTrue(!d.isActive && !d.isCompleted)
        assertEquals(d.await(), 42) // starts computing
        assertTrue(!d.isActive && d.isCompleted && !d.isCancelled)
        finish(8)
    }

    @Test
    fun testSimpleException() = runTest(
        expected = { it is TestException }
    ) {
        expect(1)
        val d = async(start = CoroutineStart.LAZY) {
            finish(3)
            throw TestException()
        }
        expect(2)
        assertTrue(!d.isActive && !d.isCompleted)
        d.await() // will throw IOException
    }

    @Test
    fun testLazyDeferAndYieldException() =  runTest(
        expected = { it is TestException }
    ) {
        expect(1)
        val d = async(start = CoroutineStart.LAZY) {
            expect(3)
            yield() // this has not effect, because parent coroutine is waiting
            finish(4)
            throw TestException()
        }
        expect(2)
        assertTrue(!d.isActive && !d.isCompleted)
        d.await() // will throw IOException
    }

    @Test
    fun testCatchException() = runTest {
        expect(1)
        val d = async(NonCancellable, start = CoroutineStart.LAZY) {
            expect(3)
            throw TestException()
        }
        expect(2)
        assertTrue(!d.isActive && !d.isCompleted)
        try {
            d.await() // will throw IOException
        } catch (e: TestException) {
            assertTrue(!d.isActive && d.isCompleted && d.isCancelled)
            expect(4)
        }
        finish(5)
    }

    @Test
    fun testStart() = runTest {
        expect(1)
        val d = async(start = CoroutineStart.LAZY) {
            expect(4)
            42
        }
        expect(2)
        assertTrue(!d.isActive && !d.isCompleted)
        assertTrue(d.start())
        assertTrue(d.isActive && !d.isCompleted)
        expect(3)
        assertTrue(!d.start())
        yield() // yield to started coroutine
        assertTrue(!d.isActive && d.isCompleted && !d.isCancelled) // and it finishes
        expect(5)
        assertEquals(d.await(), 42) // await sees result
        finish(6)
    }

    @Test
    fun testCancelBeforeStart() = runTest(
        expected = { it is CancellationException }
    ) {
        expect(1)
        val d = async(start = CoroutineStart.LAZY) {
            expectUnreached()
            42
        }
        expect(2)
        assertTrue(!d.isActive && !d.isCompleted)
        d.cancel()
        assertTrue(!d.isActive && d.isCompleted && d.isCancelled)
        assertTrue(!d.start())
        finish(3)
        assertEquals(d.await(), 42) // await shall throw CancellationException
        expectUnreached()
    }

    @Test
    fun testCancelWhileComputing() = runTest(
        expected = { it is CancellationException }
    ) {
        expect(1)
        val d = async(start = CoroutineStart.LAZY) {
            expect(4)
            yield() // yield to main, that is going to cancel us
            expectUnreached()
            42
        }
        expect(2)
        assertTrue(!d.isActive && !d.isCompleted && !d.isCancelled)
        assertTrue(d.start())
        assertTrue(d.isActive && !d.isCompleted && !d.isCancelled)
        expect(3)
        yield() // yield to d
        expect(5)
        assertTrue(d.isActive && !d.isCompleted && !d.isCancelled)
        d.cancel()
        assertTrue(!d.isActive && d.isCancelled) // cancelling !
        assertTrue(!d.isActive && d.isCancelled) // still cancelling
        finish(6)
        assertEquals(d.await(), 42) // await shall throw CancellationException
        expectUnreached()
    }

    private class TestException : Exception()
}