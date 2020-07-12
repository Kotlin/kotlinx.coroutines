/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED", "DEPRECATION") // KT-21913

package kotlinx.coroutines

import kotlin.test.*

class CompletableDeferredTest : TestBase() {
    @Test
    fun testFresh() {
        val c = CompletableDeferred<String>()
        checkFresh(c)
    }

    @Test
    fun testComplete() {
        val c = CompletableDeferred<String>()
        assertEquals(true, c.complete("OK"))
        checkCompleteOk(c)
        assertEquals("OK", c.getCompleted())
        assertEquals(false, c.complete("OK"))
        checkCompleteOk(c)
        assertEquals("OK", c.getCompleted())
    }

    @Test
    fun testCompleteWithIncompleteResult() {
        val c = CompletableDeferred<DisposableHandle>()
        assertEquals(true, c.complete(c.invokeOnCompletion {  }))
        checkCompleteOk(c)
        assertEquals(false,  c.complete(c.invokeOnCompletion {  }))
        checkCompleteOk(c)
        assertTrue(c.getCompleted() is Incomplete)
    }

    private fun checkFresh(c: CompletableDeferred<*>) {
        assertEquals(true, c.isActive)
        assertEquals(false, c.isCancelled)
        assertEquals(false, c.isCompleted)
        assertThrows<IllegalStateException> { c.getCancellationException() }
        assertThrows<IllegalStateException> { c.getCompleted() }
        assertThrows<IllegalStateException> { c.getCompletionExceptionOrNull() }
    }

    private fun checkCompleteOk(c: CompletableDeferred<*>) {
        assertEquals(false, c.isActive)
        assertEquals(false, c.isCancelled)
        assertEquals(true, c.isCompleted)
        assertTrue(c.getCancellationException() is JobCancellationException)
        assertNull(c.getCompletionExceptionOrNull())
    }

    private fun checkCancel(c: CompletableDeferred<String>) {
        assertEquals(false, c.isActive)
        assertEquals(true, c.isCancelled)
        assertEquals(true, c.isCompleted)
        assertThrows<CancellationException> { c.getCompleted() }
        assertTrue(c.getCompletionExceptionOrNull() is CancellationException)
    }

    @Test
    fun testCancelWithException() {
        val c = CompletableDeferred<String>()
        assertEquals(true, c.completeExceptionally(TestException()))
        checkCancelWithException(c)
        assertEquals(false, c.completeExceptionally(TestException()))
        checkCancelWithException(c)
    }

    private fun checkCancelWithException(c: CompletableDeferred<String>) {
        assertEquals(false, c.isActive)
        assertEquals(true, c.isCancelled)
        assertEquals(true, c.isCompleted)
        assertTrue(c.getCancellationException() is JobCancellationException)
        assertThrows<TestException> { c.getCompleted() }
        assertTrue(c.getCompletionExceptionOrNull() is TestException)
    }

    @Test
    fun testCompleteWithResultOK() {
        val c = CompletableDeferred<String>()
        assertEquals(true, c.completeWith(Result.success("OK")))
        checkCompleteOk(c)
        assertEquals("OK", c.getCompleted())
        assertEquals(false, c.completeWith(Result.success("OK")))
        checkCompleteOk(c)
        assertEquals("OK", c.getCompleted())
    }

    @Test
    fun testCompleteWithResultException() {
        val c = CompletableDeferred<String>()
        assertEquals(true, c.completeWith(Result.failure(TestException())))
        checkCancelWithException(c)
        assertEquals(false, c.completeWith(Result.failure(TestException())))
        checkCancelWithException(c)
    }

    @Test
    fun testParentCancelsChild() {
        val parent = Job()
        val c = CompletableDeferred<String>(parent)
        checkFresh(c)
        parent.cancel()
        assertEquals(false, parent.isActive)
        assertEquals(true, parent.isCancelled)
        assertEquals(false, c.isActive)
        assertEquals(true, c.isCancelled)
        assertEquals(true, c.isCompleted)
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
    fun testParentCancelledOnChildException() {
        val parent = Job()
        val c = CompletableDeferred<String>(parent)
        checkFresh(c)
        assertEquals(true, parent.isActive)
        assertEquals(true, c.completeExceptionally(TestException()))
        checkCancelWithException(c)
        assertEquals(false, parent.isActive)
        assertEquals(true, parent.isCancelled)
    }

    @Test
    fun testParentActiveOnChildCancellation() {
        val parent = Job()
        val c = CompletableDeferred<String>(parent)
        checkFresh(c)
        assertEquals(true, parent.isActive)
        c.cancel()
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
}