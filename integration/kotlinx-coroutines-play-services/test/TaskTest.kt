/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.tasks

import com.google.android.gms.tasks.RuntimeExecutionException
import com.google.android.gms.tasks.Tasks
import kotlinx.coroutines.experimental.CancellationException
import kotlinx.coroutines.experimental.CoroutineStart
import kotlinx.coroutines.experimental.Deferred
import kotlinx.coroutines.experimental.GlobalScope
import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.async
import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.ignoreLostThreads
import kotlinx.coroutines.experimental.runBlocking
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
    fun `Completed deferred as task`() = runBlocking {
        expect(1)
        val deferred = async(coroutineContext, CoroutineStart.UNDISPATCHED) {
            expect(2) // Completed immediately
            "OK"
        }
        expect(3)
        val task = deferred.asTask()
        Assert.assertThat(task.await(), IsEqual("OK"))
        finish(4)
    }

    @Test
    fun `Deferred as task`() = runBlocking {
        expect(1)
        val deferred = async(coroutineContext) {
            expect(3) // Completed later
            "OK"
        }
        expect(2)
        val task = deferred.asTask()
        Assert.assertThat(task.await(), IsEqual("OK"))
        finish(4)
    }

    @Test
    fun `Threw cancellation exception as task`() {
        val deferred = GlobalScope.async {
            throw CancellationException()
        }

        val task = deferred.asTask()
        try {
            runBlocking { task.await() }
        } catch (e: Exception) {
            Assert.assertTrue(e is CancellationException)
            Assert.assertFalse(task.isSuccessful)
            Assert.assertFalse(task.isCanceled)
        }
    }

    @Test
    fun `Cancelled as task`() {
        val deferred = GlobalScope.async {
            delay(100)
        }.apply { cancel() }

        val task = deferred.asTask()
        try {
            runBlocking { task.await() }
        } catch (e: Exception) {
            Assert.assertTrue(e is CancellationException)
            Assert.assertTrue(task.isCanceled)
        }
    }

    @Test
    fun `Threw as task`() {
        val deferred = GlobalScope.async {
            throw OutOfMemoryError()
        }

        val task = deferred.asTask()
        try {
            runBlocking { task.await() }
        } catch (e: RuntimeExecutionException) {
            Assert.assertFalse(task.isSuccessful)
            Assert.assertTrue(e.cause is OutOfMemoryError)
        }
    }

    @Test
    fun `Task stages as task`() = runBlocking {
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
    fun `Task as deferred`() = runBlocking {
        val deferred = Tasks.forResult(42).asDeferred()
        Assert.assertEquals(42, deferred.await())
    }

    @Test
    fun `Cancelled task as deferred`() = runBlocking {
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
    fun `Failed task as deferred`() = runBlocking {
        val deferred = Tasks.forException<Int>(TestException("something went wrong")).asDeferred()

        Assert.assertTrue(deferred.isCompletedExceptionally)
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
    fun `Failed task stages as deferred`() = runBlocking {
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
