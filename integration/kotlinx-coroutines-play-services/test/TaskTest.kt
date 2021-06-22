/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.tasks

import com.google.android.gms.tasks.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.locks.*
import kotlin.concurrent.*
import kotlin.test.*

class TaskTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("ForkJoinPool.commonPool-worker-")
    }

    @Test
    fun testCompletedDeferredAsTask() = runTest {
        expect(1)
        val deferred = async(start = CoroutineStart.UNDISPATCHED) {
            expect(2) // Completed immediately
            "OK"
        }
        expect(3)
        val task = deferred.asTask()
        assertEquals("OK", task.await())
        finish(4)
    }

    @Test
    fun testDeferredAsTask() = runTest {
        expect(1)
        val deferred = async {
            expect(3) // Completed later
            "OK"
        }
        expect(2)
        val task = deferred.asTask()
        assertEquals("OK", task.await())
        finish(4)
    }

    @Test
    fun testCancelledAsTask() {
        val deferred = GlobalScope.async {
            delay(100)
        }.apply { cancel() }

        val task = deferred.asTask()
        try {
            runTest { task.await() }
        } catch (e: Exception) {
            assertTrue(e is CancellationException)
            assertTrue(task.isCanceled)
        }
    }

    @Test
    fun testThrowingAsTask() {
        val deferred = GlobalScope.async<Int> {
            throw TestException("Fail")
        }

        val task = deferred.asTask()
        runTest(expected = { it is TestException }) {
            task.await()
        }
    }

    @Test
    fun testStateAsTask() = runTest {
        val lock = ReentrantLock().apply { lock() }

        val deferred: Deferred<Int> = Tasks.call {
            lock.withLock { 42 }
        }.asDeferred()

        assertFalse(deferred.isCompleted)
        lock.unlock()

        assertEquals(42, deferred.await())
        assertTrue(deferred.isCompleted)
    }

    @Test
    fun testTaskAsDeferred() = runTest {
        val deferred = Tasks.forResult(42).asDeferred()
        assertEquals(42, deferred.await())
    }

    @Test
    fun testNullResultTaskAsDeferred() = runTest {
        assertNull(Tasks.forResult(null).asDeferred().await())
    }

    @Test
    fun testCancelledTaskAsDeferred() = runTest {
        val deferred = Tasks.forCanceled<Int>().asDeferred()

        assertTrue(deferred.isCancelled)
        try {
            deferred.await()
            fail("deferred.await() should be cancelled")
        } catch (e: Exception) {
            assertTrue(e is CancellationException)
        }
    }

    @Test
    fun testFailedTaskAsDeferred() = runTest {
        val deferred = Tasks.forException<Int>(TestException("something went wrong")).asDeferred()

        assertTrue(deferred.isCancelled && deferred.isCompleted)
        val completionException = deferred.getCompletionExceptionOrNull()!!
        assertTrue(completionException is TestException)
        assertEquals("something went wrong", completionException.message)

        try {
            deferred.await()
            fail("deferred.await() should throw an exception")
        } catch (e: Exception) {
            assertTrue(e is TestException)
            assertEquals("something went wrong", e.message)
        }
    }

    @Test
    fun testFailingTaskAsDeferred() = runTest {
        val lock = ReentrantLock().apply { lock() }

        val deferred: Deferred<Int> = Tasks.call {
            lock.withLock { throw TestException("something went wrong") }
        }.asDeferred()

        assertFalse(deferred.isCompleted)
        lock.unlock()

        try {
            deferred.await()
            fail("deferred.await() should throw an exception")
        } catch (e: Exception) {
            assertTrue(e is TestException)
            assertEquals("something went wrong", e.message)
            assertSame(e.cause, deferred.getCompletionExceptionOrNull()) // debug mode stack augmentation
        }
    }

    @Test
    fun testCancellableTaskAsDeferred() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        val deferred = Tasks.forResult(42).asDeferred(cancellationTokenSource)
        assertEquals(42, deferred.await())
        assertTrue(cancellationTokenSource.token.isCancellationRequested)
    }

    @Test
    fun testNullResultCancellableTaskAsDeferred() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        assertNull(Tasks.forResult(null).asDeferred(cancellationTokenSource).await())
        assertTrue(cancellationTokenSource.token.isCancellationRequested)
    }

    @Test
    fun testCancelledCancellableTaskAsDeferred() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        val deferred = Tasks.forCanceled<Int>().asDeferred(cancellationTokenSource)

        assertTrue(deferred.isCancelled)
        try {
            deferred.await()
            fail("deferred.await() should be cancelled")
        } catch (e: Exception) {
            assertTrue(e is CancellationException)
        }
        assertTrue(cancellationTokenSource.token.isCancellationRequested)
    }

    @Test
    fun testCancellingCancellableTaskAsDeferred() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        val task = TaskCompletionSource<Int>(cancellationTokenSource.token).task
        val deferred = task.asDeferred(cancellationTokenSource)

        deferred.cancel()
        try {
            deferred.await()
            fail("deferred.await() should be cancelled")
        } catch (e: Exception) {
            assertTrue(e is CancellationException)
        }
        assertTrue(cancellationTokenSource.token.isCancellationRequested)
    }

    @Test
    fun testExternallyCancelledCancellableTaskAsDeferred() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        val task = TaskCompletionSource<Int>(cancellationTokenSource.token).task
        val deferred = task.asDeferred(cancellationTokenSource)

        cancellationTokenSource.cancel()

        try {
            deferred.await()
            fail("deferred.await() should be cancelled")
        } catch (e: Exception) {
            assertTrue(e is CancellationException)
        }
        assertTrue(cancellationTokenSource.token.isCancellationRequested)
    }

    @Test
    fun testSeparatelyCancelledCancellableTaskAsDeferred() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        val task = TaskCompletionSource<Int>().task
        task.asDeferred(cancellationTokenSource)

        cancellationTokenSource.cancel()

        assertTrue(cancellationTokenSource.token.isCancellationRequested)
    }

    @Test
    fun testFailedCancellableTaskAsDeferred() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        val deferred = Tasks.forException<Int>(TestException("something went wrong")).asDeferred(cancellationTokenSource)

        assertTrue(deferred.isCancelled && deferred.isCompleted)
        val completionException = deferred.getCompletionExceptionOrNull()!!
        assertTrue(completionException is TestException)
        assertEquals("something went wrong", completionException.message)

        try {
            deferred.await()
            fail("deferred.await() should throw an exception")
        } catch (e: Exception) {
            assertTrue(e is TestException)
            assertEquals("something went wrong", e.message)
        }
        assertTrue(cancellationTokenSource.token.isCancellationRequested)
    }

    @Test
    fun testFailingCancellableTaskAsDeferred() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        val lock = ReentrantLock().apply { lock() }

        val deferred: Deferred<Int> = Tasks.call {
            lock.withLock { throw TestException("something went wrong") }
        }.asDeferred(cancellationTokenSource)

        assertFalse(deferred.isCompleted)
        lock.unlock()

        try {
            deferred.await()
            fail("deferred.await() should throw an exception")
        } catch (e: Exception) {
            assertTrue(e is TestException)
            assertEquals("something went wrong", e.message)
            assertSame(e.cause, deferred.getCompletionExceptionOrNull()) // debug mode stack augmentation
        }
        assertTrue(cancellationTokenSource.token.isCancellationRequested)
    }

    @Test
    fun testFastPathCompletedTaskWithCancelledTokenSourceAsDeferred() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        val deferred = Tasks.forResult(42).asDeferred(cancellationTokenSource)
        cancellationTokenSource.cancel()
        assertEquals(42, deferred.await())
    }

    @Test
    fun testAwaitCancellableTask() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        val taskCompletionSource = TaskCompletionSource<Int>(cancellationTokenSource.token)

        val deferred: Deferred<Int> = async(start = CoroutineStart.UNDISPATCHED) {
            taskCompletionSource.task.await(cancellationTokenSource)
        }

        assertFalse(deferred.isCompleted)
        taskCompletionSource.setResult(42)

        assertEquals(42, deferred.await())
        assertTrue(deferred.isCompleted)
    }

    @Test
    fun testFailedAwaitTask() = runTest(expected = { it is TestException }) {
        val cancellationTokenSource = CancellationTokenSource()
        val taskCompletionSource = TaskCompletionSource<Int>(cancellationTokenSource.token)

        val deferred: Deferred<Int> = async(start = CoroutineStart.UNDISPATCHED) {
            taskCompletionSource.task.await(cancellationTokenSource)
        }

        assertFalse(deferred.isCompleted)
        taskCompletionSource.setException(TestException("something went wrong"))

        deferred.await()
    }

    @Test
    fun testCancelledAwaitCancellableTask() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        val taskCompletionSource = TaskCompletionSource<Int>(cancellationTokenSource.token)

        val deferred: Deferred<Int> = async(start = CoroutineStart.UNDISPATCHED) {
            taskCompletionSource.task.await(cancellationTokenSource)
        }

        assertFalse(deferred.isCompleted)
        // Cancel the deferred
        deferred.cancel()

        try {
            deferred.await()
            fail("deferred.await() should be cancelled")
        } catch (e: Exception) {
            assertTrue(e is CancellationException)
        }

        assertTrue(cancellationTokenSource.token.isCancellationRequested)
    }

    @Test
    fun testExternallyCancelledAwaitCancellableTask() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        val taskCompletionSource = TaskCompletionSource<Int>(cancellationTokenSource.token)

        val deferred: Deferred<Int> = async(start = CoroutineStart.UNDISPATCHED) {
            taskCompletionSource.task.await(cancellationTokenSource)
        }

        assertFalse(deferred.isCompleted)
        // Cancel the cancellation token source
        cancellationTokenSource.cancel()

        try {
            deferred.await()
            fail("deferred.await() should be cancelled")
        } catch (e: Exception) {
            assertTrue(e is CancellationException)
        }

        assertTrue(cancellationTokenSource.token.isCancellationRequested)
    }

    @Test
    fun testFastPathCancellationTokenSourceCancelledAwaitCancellableTask() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        // Construct a task without the cancellation token source
        val taskCompletionSource = TaskCompletionSource<Int>()

        val deferred: Deferred<Int> = async(start = CoroutineStart.LAZY) {
            taskCompletionSource.task.await(cancellationTokenSource)
        }

        assertFalse(deferred.isCompleted)
        cancellationTokenSource.cancel()

        // Cancelling the token doesn't cancel the deferred
        assertTrue(cancellationTokenSource.token.isCancellationRequested)
        assertFalse(deferred.isCompleted)

        // Cleanup
        deferred.cancel()
    }

    @Test
    fun testSlowPathCancellationTokenSourceCancelledAwaitCancellableTask() = runTest {
        val cancellationTokenSource = CancellationTokenSource()
        // Construct a task without the cancellation token source
        val taskCompletionSource = TaskCompletionSource<Int>()

        val deferred: Deferred<Int> = async(start = CoroutineStart.UNDISPATCHED) {
            taskCompletionSource.task.await(cancellationTokenSource)
        }

        assertFalse(deferred.isCompleted)
        cancellationTokenSource.cancel()

        // Cancelling the token doesn't cancel the deferred
        assertTrue(cancellationTokenSource.token.isCancellationRequested)
        assertFalse(deferred.isCompleted)

        // Cleanup
        deferred.cancel()
    }

    @Test
    fun testFastPathWithCompletedTaskAndCanceledTokenSourceAwaitTask() = runTest {
        val firstCancellationTokenSource = CancellationTokenSource()
        val secondCancellationTokenSource = CancellationTokenSource()
        // Construct a task with a different cancellation token source
        val taskCompletionSource = TaskCompletionSource<Int>(firstCancellationTokenSource.token)

        val deferred: Deferred<Int> = async(start = CoroutineStart.LAZY) {
            taskCompletionSource.task.await(secondCancellationTokenSource)
        }

        assertFalse(deferred.isCompleted)
        secondCancellationTokenSource.cancel()

        assertFalse(deferred.isCompleted)
        taskCompletionSource.setResult(42)

        assertEquals(42, deferred.await())
        assertTrue(deferred.isCompleted)
    }

    class TestException(message: String) : Exception(message)
}
