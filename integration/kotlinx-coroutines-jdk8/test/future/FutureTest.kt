/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.future

import kotlinx.coroutines.*
import kotlinx.coroutines.CancellationException
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import java.util.concurrent.locks.*
import java.util.function.*
import kotlin.concurrent.*
import kotlin.coroutines.*
import kotlin.reflect.*
import kotlin.test.assertFailsWith

class FutureTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("ForkJoinPool.commonPool-worker-")
    }

    @Test
    fun testSimpleAwait() {
        val future = GlobalScope.future {
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
        val future = GlobalScope.future {
            toAwait.await() + "K"
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testCompletedCompletionStage() {
        val completable = CompletableFuture<String>()
        completable.complete("O")
        val toAwait: CompletionStage<String> = completable
        val future = GlobalScope.future {
            toAwait.await() + "K"
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testWaitForFuture() {
        val toAwait = CompletableFuture<String>()
        val future = GlobalScope.future {
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
        val future = GlobalScope.future {
            toAwait.await() + "K"
        }
        assertFalse(future.isDone)
        completable.complete("O")
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testCompletedFutureExceptionally() {
        val toAwait = CompletableFuture<String>()
        toAwait.completeExceptionally(TestException("O"))
        val future = GlobalScope.future {
            try {
                toAwait.await()
            } catch (e: TestException) {
                e.message!!
            } + "K"
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    // Test fast-path of CompletionStage.await() extension
    fun testCompletedCompletionStageExceptionally() {
        val completable = CompletableFuture<String>()
        val toAwait: CompletionStage<String> = completable
        completable.completeExceptionally(TestException("O"))
        val future = GlobalScope.future {
            try {
                toAwait.await()
            } catch (e: TestException) {
                e.message!!
            } + "K"
        }
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    // Test slow-path of CompletionStage.await() extension
    fun testWaitForFutureWithException() = runTest {
        expect(1)
        val toAwait = CompletableFuture<String>()
        val future = future(start = CoroutineStart.UNDISPATCHED) {
            try {
                expect(2)
                toAwait.await() // will suspend (slow path)
            } catch (e: TestException) {
                expect(4)
                e.message!!
            } + "K"
        }
        expect(3)
        assertFalse(future.isDone)
        toAwait.completeExceptionally(TestException("O"))
        yield() // to future coroutine
        assertThat(future.get(), IsEqual("OK"))
        finish(5)
    }

    @Test
    fun testWaitForCompletionStageWithException() {
        val completable = CompletableFuture<String>()
        val toAwait: CompletionStage<String> = completable
        val future = GlobalScope.future {
            try {
                toAwait.await()
            } catch (e: TestException) {
                e.message!!
            } + "K"
        }
        assertFalse(future.isDone)
        completable.completeExceptionally(TestException("O"))
        assertThat(future.get(), IsEqual("OK"))
    }

    @Test
    fun testExceptionInsideCoroutine() {
        val future = GlobalScope.future {
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
        val deferred = async(start = CoroutineStart.UNDISPATCHED) {
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
        val deferred = async {
            expect(3) // will complete later
            "OK"
        }
        expect(2)
        val future = deferred.asCompletableFuture()
        assertThat(future.await(), IsEqual("OK")) // await yields main thread to deferred coroutine
        finish(4)
    }

    @Test
    fun testAsCompletableFutureThrowable() {
        val deferred = GlobalScope.async {
            throw OutOfMemoryError()
        }

        val future = deferred.asCompletableFuture()
        try {
            future.get()
        } catch (e: ExecutionException) {
            assertTrue(future.isCompletedExceptionally)
            assertTrue(e.cause is OutOfMemoryError)
        }
    }

    @Test
    fun testCancellableAwaitFuture() = runBlocking {
        expect(1)
        val toAwait = CompletableFuture<String>()
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
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
        val future = GlobalScope.future(wrapContinuation {
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

        assertTrue(deferred.isCancelled)
        val completionException = deferred.getCompletionExceptionOrNull()!!
        assertTrue(completionException is TestException)
        assertEquals("something went wrong", completionException.message)

        try {
            deferred.await()
            fail("deferred.await() should throw an exception")
        } catch (e: Throwable) {
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
        } catch (e: CompletionException) {
            assertTrue(deferred.isCancelled)
            val cause = e.cause?.cause!! // Stacktrace augmentation
            assertTrue(cause is TestException)
            assertEquals("something went wrong", cause.message)
        }
    }

    private val threadLocal = ThreadLocal<String>()

    @Test
    fun testApiBridge() = runTest {
        val result = newSingleThreadContext("ctx").use {
            val future = CompletableFuture.supplyAsync(Supplier { threadLocal.set("value") }, it.executor)
            val job = async(it) {
                future.await()
                threadLocal.get()
            }

            job.await()
        }

        assertEquals("value", result)
    }

    @Test
    fun testFutureCancellation() = runTest {
        val future = awaitFutureWithCancel(true)
        assertTrue(future.isCompletedExceptionally)
        assertFailsWith<CancellationException> { future.get() }
        finish(4)
    }

    @Test
    fun testNoFutureCancellation() = runTest {
        val future = awaitFutureWithCancel(false)
        assertFalse(future.isCompletedExceptionally)
        assertEquals(239, future.get())
        finish(4)
    }

    private suspend fun CoroutineScope.awaitFutureWithCancel(cancellable: Boolean): CompletableFuture<Int> {
        val latch = CountDownLatch(1)
        val future = CompletableFuture.supplyAsync {
            latch.await()
            239
        }

        val deferred = async {
            expect(2)
            if (cancellable) future.await()
            else future.asDeferred().await()
        }
        expect(1)
        yield()
        deferred.cancel()
        expect(3)
        latch.countDown()
        return future
    }

    @Test
    fun testChildException() = runTest {
        val result = future(Dispatchers.Unconfined) {
            // child crashes
            launch { throw TestException("FAIL") }
            42
        }

        result.checkFutureException<TestException>()
    }

    @Test
    fun testExceptionAggregation() = runTest {
        val result = future(Dispatchers.Unconfined) {
            // child crashes
            launch(start = CoroutineStart.ATOMIC) { throw TestException1("FAIL") }
            launch(start = CoroutineStart.ATOMIC) { throw TestException2("FAIL") }
            throw TestException()
        }

        expect(1)
        result.checkFutureException<TestException>(TestException1::class, TestException2::class)
        yield()
        finish(2) // we are not cancelled
    }

    @Test
    fun testExternalCompletion() = runTest {
        expect(1)
        val result = future(Dispatchers.Unconfined) {
            try {
                delay(Long.MAX_VALUE)
            } finally {
                expect(2)
            }
        }

        result.complete(Unit)
        finish(3)
    }

    @Test
    fun testExceptionOnExternalCompletion() = runTest(expected = {it is TestException}) {
        expect(1)
        val result = future(Dispatchers.Unconfined) {
            try {
                delay(Long.MAX_VALUE)
            } finally {
                expect(2)
                throw TestException()
            }
        }

        result.complete(Unit)
        finish(3)
    }

    /**
     * See [https://github.com/Kotlin/kotlinx.coroutines/issues/892]
     */
    @Test
    fun testTimeoutCancellationFailRace() {
        repeat(10 * stressTestMultiplier) {
            runBlocking {
                withTimeoutOrNull(10) {
                    while (true) {
                        var caught = false
                        try {
                            CompletableFuture.supplyAsync {
                                throw TestException()
                            }.await()
                        } catch (ignored: TestException) {
                            caught = true
                        }
                        assertTrue(caught) // should have caught TestException or timed out
                    }
                }
            }
        }
    }

    private inline fun <reified T: Throwable> CompletableFuture<*>.checkFutureException(vararg suppressed: KClass<out Throwable>) {
        val e = assertFailsWith<ExecutionException> { get() }
        val cause = e.cause!!
        assertTrue(cause is T)
        for ((index, clazz) in suppressed.withIndex()) {
            assertTrue(clazz.isInstance(cause.suppressed[index]))
        }
    }

    private fun wrapContinuation(wrapper: (() -> Unit) -> Unit): CoroutineDispatcher = object : CoroutineDispatcher() {
        override fun dispatch(context: CoroutineContext, block: Runnable) {
            wrapper {
                block.run()
            }
        }
    }
}
