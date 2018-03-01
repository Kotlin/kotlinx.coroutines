/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.future

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.CancellationException
import org.hamcrest.core.IsEqual
import org.junit.Assert.*
import org.junit.Before
import org.junit.Test
import java.util.concurrent.*
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.locks.ReentrantLock
import kotlin.concurrent.withLock
import kotlin.coroutines.experimental.CoroutineContext

class FutureTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("ForkJoinPool.commonPool-worker-")
    }

    @Test
    fun testSimpleAwait() {
        val future = future {
            CompletableFuture.supplyAsync {
                "O"
            }.await() + "K"
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testCompletedFuture() {
        val toAwait = CompletableFuture<String>()
        toAwait.complete("O")
        val future = future {
            toAwait.await() + "K"
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testCompletedCompletionStage() {
        val completable = CompletableFuture<String>()
        completable.complete("O")
        val toAwait: CompletionStage<String> = completable
        val future = future {
            toAwait.await() + "K"
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testWaitForFuture() {
        val toAwait = CompletableFuture<String>()
        val future = future {
            toAwait.await() + "K"
        }
        assertFalse(future.isDone)
        toAwait.complete("O")
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testWaitForCompletionStage() {
        val completable = CompletableFuture<String>()
        val toAwait: CompletionStage<String> = completable
        val future = future {
            toAwait.await() + "K"
        }
        assertFalse(future.isDone)
        completable.complete("O")
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testCompletedFutureExceptionally() {
        val toAwait = CompletableFuture<String>()
        toAwait.completeExceptionally(RuntimeException("O"))
        val future = future<String> {
            try {
                toAwait.await()
            } catch (e: RuntimeException) {
                e.message!!
            } + "K"
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testCompletedCompletionStageExceptionally() {
        val completable = CompletableFuture<String>()
        val toAwait: CompletionStage<String> = completable
        completable.completeExceptionally(RuntimeException("O"))
        val future = future<String> {
            try {
                toAwait.await()
            } catch (e: RuntimeException) {
                e.message!!
            } + "K"
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testWaitForFutureWithException() {
        val toAwait = CompletableFuture<String>()
        val future = future<String> {
            try {
                toAwait.await()
            } catch (e: RuntimeException) {
                e.message!!
            } + "K"
        }
        assertFalse(future.isDone)
        toAwait.completeExceptionally(RuntimeException("O"))
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testWaitForCompletionStageWithException() {
        val completable = CompletableFuture<String>()
        val toAwait: CompletionStage<String> = completable
        val future = future<String> {
            try {
                toAwait.await()
            } catch (e: RuntimeException) {
                e.message!!
            } + "K"
        }
        assertFalse(future.isDone)
        completable.completeExceptionally(RuntimeException("O"))
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testExceptionInsideCoroutine() {
        val future = future {
            if (CompletableFuture.supplyAsync { true }.await()) {
                throw IllegalStateException("OK")
            }
            "fail"
        }
        try {
            future.get()
            fail("'get' should've throw an exception")
        } catch (e: ExecutionException) {
            assertTrue(e.cause is IllegalStateException)
            assertThat(e.cause!!.message, IsEqual("OK"))
        }
    }

    @Test
    fun testCompletedDeferredAsCompletableFuture() = runBlocking {
        expect(1)
        val deferred = async(coroutineContext, CoroutineStart.UNDISPATCHED) {
            expect(2) // completed right away
            "OK"
        }
        expect(3)
        val future = deferred.asCompletableFuture()
        assertThat(future.await(), IsEqual("OK"))
        finish(4)
    }

    @Test
    fun testWaitForDeferredAsCompletableFuture() = runBlocking {
        expect(1)
        val deferred = async(coroutineContext) {
            expect(3) // will complete later
            "OK"
        }
        expect(2)
        val future = deferred.asCompletableFuture()
        assertThat(future.await(), IsEqual("OK")) // await yields main thread to deferred coroutine
        finish(4)
    }

    @Test
    fun testCancellableAwaitFuture() = runBlocking {
        expect(1)
        val toAwait = CompletableFuture<String>()
        val job = launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                toAwait.await() // suspends
            } catch (e: CancellationException) {
                expect(5) // should throw cancellation exception
                throw e
            }
        }
        expect(3)
        job.cancel() // cancel the job
        toAwait.complete("fail") // too late, the waiting job was already cancelled
        expect(4) // job processing of cancellation was scheduled, not executed yet
        yield() // yield main thread to job
        finish(6)
    }

    @Test
    fun testContinuationWrapped() {
        val depth = AtomicInteger()
        val future = future(wrapContinuation {
            depth.andIncrement
            it()
            depth.andDecrement
        }) {
            assertEquals("Part before first suspension must be wrapped", 1, depth.get())
            val result =
                    CompletableFuture.supplyAsync {
                        while (depth.get() > 0);
                        assertEquals("Part inside suspension point should not be wrapped", 0, depth.get())
                        "OK"
                    }.await()
            assertEquals("Part after first suspension should be wrapped", 1, depth.get())
            CompletableFuture.supplyAsync {
                while (depth.get() > 0);
                assertEquals("Part inside suspension point should not be wrapped", 0, depth.get())
                "ignored"
            }.await()
            result
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testCompletableFutureStageAsDeferred() = runBlocking {
        val lock = ReentrantLock().apply { lock() }

        val deferred: Deferred<Int> = CompletableFuture.supplyAsync {
            lock.withLock { 42 }
        }.asDeferred()

        assertFalse(deferred.isCompleted)
        lock.unlock()

        assertEquals(42, deferred.await())
        assertTrue(deferred.isCompleted)
    }

    @Test
    fun testCompletedFutureAsDeferred() = runBlocking {
        val deferred: Deferred<Int> = CompletableFuture.completedFuture(42).asDeferred()
        assertEquals(42, deferred.await())
    }

    @Test
    fun testFailedFutureAsDeferred() = runBlocking {
        val future = CompletableFuture<Int>().apply {
            completeExceptionally(TestException("something went wrong"))
        }
        val deferred = future.asDeferred()

        assertTrue(deferred.isCompletedExceptionally)
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
    fun testCompletableFutureWithExceptionAsDeferred() = runBlocking {
        val lock = ReentrantLock().apply { lock() }

        val deferred: Deferred<Int> = CompletableFuture.supplyAsync {
            lock.withLock { throw TestException("something went wrong") }
        }.asDeferred()

        assertFalse(deferred.isCompleted)
        lock.unlock()

        try {
            deferred.await()
            fail("deferred.await() should throw an exception")
        } catch (e: Exception) {
            assertTrue(deferred.isCompletedExceptionally)
            assertTrue(e is CompletionException) // that's how supplyAsync wraps it
            val cause = e.cause!!
            assertTrue(cause is TestException)
            assertEquals("something went wrong", cause.message)
            assertSame(e, deferred.getCompletionExceptionOrNull()) // same exception is returns as thrown
        }
    }

    class TestException(message: String) : Exception(message)

    private fun wrapContinuation(wrapper: (() -> Unit) -> Unit): CoroutineDispatcher = object : CoroutineDispatcher() {
        override fun dispatch(context: CoroutineContext, block: Runnable) {
            wrapper {
                block.run()
            }
        }
    }
}
