/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlin.test.*

class CompletableDeferredTest : TestBase() {
    @Test
    fun testFresh() {
        val c = CompletableDeferred<String>()
        checkFresh(c)
    }

    private fun checkFresh(c: CompletableDeferred<String>) {
        assertEquals(true, c.isActive)
        assertEquals(false, c.isCancelled)
        assertEquals(false, c.isCompleted)
        assertEquals(false, c.isCompletedExceptionally)
        assertThrows<IllegalStateException> { c.getCancellationException() }
        assertThrows<IllegalStateException> { c.getCompleted() }
        assertThrows<IllegalStateException> { c.getCompletionExceptionOrNull() }
    }

    @Test
    fun testComplete() {
        val c = CompletableDeferred<String>()
        assertEquals(true, c.complete("OK"))
        checkCompleteOk(c)
        assertEquals(false, c.complete("OK"))
        checkCompleteOk(c)
    }

    private fun checkCompleteOk(c: CompletableDeferred<String>) {
        assertEquals(false, c.isActive)
        assertEquals(false, c.isCancelled)
        assertEquals(true, c.isCompleted)
        assertEquals(false, c.isCompletedExceptionally)
        assertTrue(c.getCancellationException() is JobCancellationException)
        assertEquals("OK", c.getCompleted())
        assertEquals(null, c.getCompletionExceptionOrNull())
    }

    @Test
    fun testCompleteWithException() {
        val c = CompletableDeferred<String>()
        assertEquals(true, c.completeExceptionally(TestException()))
        checkCompleteTestException(c)
        assertEquals(false, c.completeExceptionally(TestException()))
        checkCompleteTestException(c)
    }

    private fun checkCompleteTestException(c: CompletableDeferred<String>) {
        assertEquals(false, c.isActive)
        assertEquals(false, c.isCancelled)
        assertEquals(true, c.isCompleted)
        assertEquals(true, c.isCompletedExceptionally)
        assertTrue(c.getCancellationException() is JobCancellationException)
        assertThrows<TestException> { c.getCompleted() }
        assertTrue(c.getCompletionExceptionOrNull() is TestException)
    }

    @Test
    fun testCancel() {
        val c = CompletableDeferred<String>()
        assertEquals(true, c.cancel())
        checkCancel(c)
        assertEquals(false, c.cancel())
        checkCancel(c)
    }

    private fun checkCancel(c: CompletableDeferred<String>) {
        assertEquals(false, c.isActive)
        assertEquals(true, c.isCancelled)
        assertEquals(true, c.isCompleted)
        assertEquals(true, c.isCompletedExceptionally)
        assertThrows<CancellationException> { c.getCompleted() }
        assertTrue(c.getCompletionExceptionOrNull() is CancellationException)
    }

    @Test
    fun testCancelWithException() {
        val c = CompletableDeferred<String>()
        assertEquals(true, c.cancel(TestException()))
        checkCancelWithException(c)
        assertEquals(false, c.cancel(TestException()))
        checkCancelWithException(c)
    }

    private fun checkCancelWithException(c: CompletableDeferred<String>) {
        assertEquals(false, c.isActive)
        assertEquals(true, c.isCancelled)
        assertEquals(true, c.isCompleted)
        assertEquals(true, c.isCompletedExceptionally)
        assertTrue(c.getCancellationException() is JobCancellationException)
        assertThrows<TestException> { c.getCompleted() }
        assertTrue(c.getCompletionExceptionOrNull() is TestException)
    }

    @Test
    fun testParentFailsChild() {
        val parent = Job()
        val c = CompletableDeferred<String>(parent)
        checkFresh(c)
        parent.cancel()
        assertEquals(false, parent.isActive)
        assertEquals(true, parent.isCancelled)
        assertEquals(false, c.isActive)
        assertEquals(false, c.isCancelled)
        assertEquals(true, c.isCompleted)
        assertEquals(true, c.isCompletedExceptionally)
        assertThrows<CancellationException> { c.getCompleted() }
        assertTrue(c.getCompletionExceptionOrNull() is CancellationException)
    }

    @Test
    fun testParentActiveOnChildCompletion() {
        val parent = Job()
        val c = CompletableDeferred<String>(parent)
        checkFresh(c)
        assertEquals(true, parent.isActive)
        assertEquals(true, c.complete("OK"))
        checkCompleteOk(c)
        assertEquals(true, parent.isActive)
    }

    @Test
    fun testParentActiveOnChildException() {
        val parent = Job()
        val c = CompletableDeferred<String>(parent)
        checkFresh(c)
        assertEquals(true, parent.isActive)
        assertEquals(true, c.completeExceptionally(TestException()))
        checkCompleteTestException(c)
        assertEquals(true, parent.isActive)
    }

    @Test
    fun testParentActiveOnChildCancellation() {
        val parent = Job()
        val c = CompletableDeferred<String>(parent)
        checkFresh(c)
        assertEquals(true, parent.isActive)
        assertEquals(true, c.cancel())
        checkCancel(c)
        assertEquals(true, parent.isActive)
    }

    @Test
    fun testAwait() = runTest {
        expect(1)
        val c = CompletableDeferred<String>()
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            assertEquals("OK", c.await()) // suspends
            expect(5)
            assertEquals("OK", c.await()) // does not suspend
            expect(6)
        }
        expect(3)
        c.complete("OK")
        expect(4)
        yield() // to launch
        finish(7)
    }

    @Test
    fun testCancelAndAwaitParentWaitChildren() = runTest {
        expect(1)
        val parent = CompletableDeferred<String>()
        launch(parent, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                yield() // will get cancelled
            } finally {
                expect(5)
            }
        }
        expect(3)
        parent.cancel()
        expect(4)
        try {
            parent.await()
        } catch (e: CancellationException) {
            finish(6)
        }
    }

    @Test
    fun testCompleteAndAwaitParentWaitChildren() = runTest {
        expect(1)
        val parent = CompletableDeferred<String>()
        launch(parent, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                yield() // will get cancelled
            } finally {
                expect(5)
            }
        }
        expect(3)
        parent.complete("OK")
        expect(4)
        assertEquals("OK", parent.await())
        finish(6)
    }

    private inline fun <reified T: Throwable> assertThrows(block: () -> Unit) {
        try {
            block()
            fail("Should not complete normally")
        } catch (e: Throwable) {
            assertTrue(e is T)
        }
    }

    class TestException : Throwable()
}