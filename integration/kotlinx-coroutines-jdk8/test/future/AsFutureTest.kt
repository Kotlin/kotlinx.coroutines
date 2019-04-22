/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.future

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Assert.*
import java.util.concurrent.*
import java.util.concurrent.CancellationException

class AsFutureTest : TestBase() {

    @Test
    fun testCompletedDeferredAsCompletableFuture() = runTest {
        expect(1)
        val deferred = async(start = CoroutineStart.UNDISPATCHED) {
            expect(2) // completed right away
            "OK"
        }
        expect(3)
        val future = deferred.asCompletableFuture()
        assertEquals("OK", future.await())
        finish(4)
    }

    @Test
    fun testCompletedJobAsCompletableFuture() = runTest {
        val job = Job().apply { complete() }
        val future = job.asCompletableFuture()
        assertEquals(Unit, future.await())
    }

    @Test
    fun testWaitForDeferredAsCompletableFuture() = runTest {
        expect(1)
        val deferred = async {
            expect(3) // will complete later
            "OK"
        }
        expect(2)
        val future = deferred.asCompletableFuture()
        assertEquals("OK", future.await()) // await yields main thread to deferred coroutine
        finish(4)
    }

    @Test
    fun testWaitForJobAsCompletableFuture() = runTest {
        val job = Job()
        val future = job.asCompletableFuture()
        assertTrue(job.isActive)
        job.complete()
        assertFalse(job.isActive)
        assertEquals(Unit, future.await())
    }

    @Test
    fun testAsCompletableFutureThrowable() {
        val deferred = GlobalScope.async<Unit> { throw OutOfMemoryError() }
        val future = deferred.asCompletableFuture()
        try {
            expect(1)
            future.get()
            expectUnreached()
        } catch (e: ExecutionException) {
            assertTrue(future.isCompletedExceptionally)
            assertTrue(e.cause is OutOfMemoryError)
            finish(2)
        }
    }

    @Test
    fun testJobAsCompletableFutureThrowable() {
        val job = Job()
        CompletableDeferred<Unit>(parent = job).apply { completeExceptionally(OutOfMemoryError()) }
        val future = job.asCompletableFuture()
        try {
            expect(1)
            future.get()
            expectUnreached()
        } catch (e: ExecutionException) {
            assertTrue(future.isCompletedExceptionally)
            assertTrue(e.cause is OutOfMemoryError)
            finish(2)
        }
    }

    @Test
    fun testJobAsCompletableFutureCancellation() {
        val job = Job()
        val future = job.asCompletableFuture()
        job.cancel()
        try {
            expect(1)
            future.get()
            expectUnreached()
        } catch (e: CancellationException) {
            assertTrue(future.isCompletedExceptionally)
            finish(2)
        }
    }

    @Test
    fun testJobCancellation() {
        val job = Job()
        val future = job.asCompletableFuture()
        future.cancel(true)
        assertTrue(job.isCancelled)
        assertTrue(job.isCompleted)
        assertFalse(job.isActive)
    }

    @Test
    fun testDeferredCancellation() {
        val deferred = CompletableDeferred<Int>()
        val future = deferred.asCompletableFuture()
        future.cancel(true)
        assertTrue(deferred.isCancelled)
        assertTrue(deferred.isCompleted)
        assertFalse(deferred.isActive)
        assertTrue(deferred.getCompletionExceptionOrNull() is CancellationException)
    }
}
