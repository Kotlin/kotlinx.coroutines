/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.tasks

import com.google.android.gms.tasks.RuntimeExecutionException
import com.google.android.gms.tasks.Tasks
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.CoroutineStart
import kotlinx.coroutines.Deferred
import kotlinx.coroutines.GlobalScope
import kotlinx.coroutines.TestBase
import kotlinx.coroutines.async
import kotlinx.coroutines.delay
import kotlinx.coroutines.ignoreLostThreads
import org.hamcrest.core.IsEqual
import org.junit.Assert
import org.junit.Before
import org.junit.Test
import java.util.concurrent.locks.ReentrantLock
import kotlin.concurrent.withLock

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
        Assert.assertThat(task.await(), IsEqual("OK"))
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
        Assert.assertThat(task.await(), IsEqual("OK"))
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
            Assert.assertTrue(e is CancellationException)
            Assert.assertTrue(task.isCanceled)
        }
    }

    @Test
    fun testThrowingAsTask() {
        val deferred = GlobalScope.async {
            throw OutOfMemoryError()
        }

        val task = deferred.asTask()
        try {
            runTest { task.await() }
        } catch (e: RuntimeExecutionException) {
            Assert.assertFalse(task.isSuccessful)
            Assert.assertTrue(e.cause is OutOfMemoryError)
        }
    }

    @Test
    fun testStateAsTask() = runTest {
        val lock = ReentrantLock().apply { lock() }

        val deferred: Deferred<Int> = Tasks.call {
            lock.withLock { 42 }
        }.asDeferred()

        Assert.assertFalse(deferred.isCompleted)
        lock.unlock()

        Assert.assertEquals(42, deferred.await())
        Assert.assertTrue(deferred.isCompleted)
    }

    @Test
    fun testTaskAsDeferred() = runTest {
        val deferred = Tasks.forResult(42).asDeferred()
        Assert.assertEquals(42, deferred.await())
    }

    @Test
    fun testCancelledTaskAsDeferred() = runTest {
        val deferred = Tasks.forCanceled<Int>().asDeferred()

        Assert.assertTrue(deferred.isCancelled)
        try {
            deferred.await()
            Assert.fail("deferred.await() should be cancelled")
        } catch (e: Exception) {
            Assert.assertTrue(e is CancellationException)
        }
    }

    @Test
    fun testFailedTaskAsDeferred() = runTest {
        val deferred = Tasks.forException<Int>(TestException("something went wrong")).asDeferred()

        Assert.assertTrue(deferred.isCancelled && deferred.isCompleted)
        val completionException = deferred.getCompletionExceptionOrNull()!!
        Assert.assertTrue(completionException is TestException)
        Assert.assertEquals("something went wrong", completionException.message)

        try {
            deferred.await()
            Assert.fail("deferred.await() should throw an exception")
        } catch (e: Exception) {
            Assert.assertTrue(e is TestException)
            Assert.assertEquals("something went wrong", e.message)
        }
    }

    @Test
    fun testFailingTaskAsDeferred() = runTest {
        val lock = ReentrantLock().apply { lock() }

        val deferred: Deferred<Int> = Tasks.call {
            lock.withLock { throw TestException("something went wrong") }
        }.asDeferred()

        Assert.assertFalse(deferred.isCompleted)
        lock.unlock()

        try {
            deferred.await()
            Assert.fail("deferred.await() should throw an exception")
        } catch (e: Exception) {
            Assert.assertTrue(e is TestException)
            Assert.assertEquals("something went wrong", e.message)
            Assert.assertSame(e, deferred.getCompletionExceptionOrNull())
        }
    }

    class TestException(message: String) : Exception(message)
}
