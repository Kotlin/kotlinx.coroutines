/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
        val deferred = GlobalScope.async {
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

    class TestException(message: String) : Exception(message)
}
