/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.guava

import com.google.common.util.concurrent.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Ignore
import org.junit.Test
import java.util.concurrent.*
import java.util.concurrent.CancellationException
import kotlin.test.*

class ListenableFutureTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("ForkJoinPool.commonPool-worker-")
    }

    @Test
    fun testSimpleAwait() {
        val service = MoreExecutors.listeningDecorator(ForkJoinPool.commonPool())
        val future = GlobalScope.future {
            service.submit(Callable<String> {
                "O"
            }).await() + "K"
        }
        assertEquals("OK", future.get())
    }

    @Test
    fun testAwaitWithContext() = runTest {
        val future = SettableFuture.create<Int>()
        val deferred = async {
            withContext(Dispatchers.Default) {
                future.await()
            }
        }

        future.set(1)
        assertEquals(1, deferred.await())
    }

    @Test
    fun testAwaitWithCancellation() = runTest(expected = {it is TestCancellationException}) {
        val future = SettableFuture.create<Int>()
        val deferred = async {
            withContext(Dispatchers.Default) {
                future.await()
            }
        }

        deferred.cancel(TestCancellationException())
        deferred.await() // throws TCE
        expectUnreached()
    }

    @Test
    fun testCompletedFuture() {
        val toAwait = SettableFuture.create<String>()
        toAwait.set("O")
        val future = GlobalScope.future {
            toAwait.await() + "K"
        }
        assertEquals("OK", future.get())
    }

    @Test
    fun testWaitForFuture() {
        val toAwait = SettableFuture.create<String>()
        val future = GlobalScope.future {
            toAwait.await() + "K"
        }
        assertFalse(future.isDone)
        toAwait.set("O")
        assertEquals("OK", future.get())
    }

    @Test
    fun testCompletedFutureExceptionally() {
        val toAwait = SettableFuture.create<String>()
        toAwait.setException(IllegalArgumentException("O"))
        val future = GlobalScope.future {
            try {
                toAwait.await()
            } catch (e: RuntimeException) {
                assertTrue(e is IllegalArgumentException)
                e.message!!
            } + "K"
        }
        assertEquals("OK", future.get())
    }

    @Test
    fun testWaitForFutureWithException() {
        val toAwait = SettableFuture.create<String>()
        val future = GlobalScope.future {
            try {
                toAwait.await()
            } catch (e: RuntimeException) {
                assertTrue(e is IllegalArgumentException)
                e.message!!
            } + "K"
        }
        assertFalse(future.isDone)
        toAwait.setException(IllegalArgumentException("O"))
        assertEquals("OK", future.get())
    }

    @Test
    fun testExceptionInsideCoroutine() {
        val service = MoreExecutors.listeningDecorator(ForkJoinPool.commonPool())
        val future = GlobalScope.future {
            if (service.submit(Callable<Boolean> { true }).await()) {
                throw IllegalStateException("OK")
            }
            "fail"
        }
        try {
            future.get()
            fail("'get' should've throw an exception")
        } catch (e: ExecutionException) {
            assertTrue(e.cause is IllegalStateException)
            assertEquals("OK", e.cause!!.message)
        }
    }

    @Test
    fun testFutureLazyStartThrows() {
        expect(1)
        val e = assertFailsWith<IllegalArgumentException> {
            GlobalScope.future(start = CoroutineStart.LAZY) {}
        }

        assertEquals("LAZY start is not supported", e.message)
        finish(2)
    }

    @Test
    fun testCompletedDeferredAsListenableFuture() = runBlocking {
        expect(1)
        val deferred = async(start = CoroutineStart.UNDISPATCHED) {
            expect(2) // completed right away
            "OK"
        }
        expect(3)
        val future = deferred.asListenableFuture()
        assertEquals("OK", future.await())
        finish(4)
    }

    @Test
    fun testWaitForDeferredAsListenableFuture() = runBlocking {
        expect(1)
        val deferred = async {
            expect(3) // will complete later
            "OK"
        }
        expect(2)
        val future = deferred.asListenableFuture()
        assertEquals("OK", future.await()) // await yields main thread to deferred coroutine
        finish(4)
    }

    @Test
    fun testAsListenableFutureThrowable() {
        val deferred = GlobalScope.async {
            throw OutOfMemoryError()
        }

        val future = deferred.asListenableFuture()
        try {
            future.get()
        } catch (e: ExecutionException) {
            assertTrue(future.isDone)
            assertTrue(e.cause is OutOfMemoryError)
        }
    }

    @Test
    fun testCancellableAwait() = runBlocking {
        expect(1)
        val toAwait = SettableFuture.create<String>()
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
        toAwait.set("fail") // too late, the waiting job was already cancelled
        expect(4) // job processing of cancellation was scheduled, not executed yet
        yield() // yield main thread to job
        finish(6)
    }

    @Test
    fun testFutureAwaitCancellationPropagatingToDeferred() = runTest {

        val latch = CountDownLatch(1)
        val executor = MoreExecutors.listeningDecorator(ForkJoinPool.commonPool())
        val future = executor.submit(Callable { latch.await(); 42 })
        val deferred = async {
            expect(2)
            future.await()
        }
        expect(1)
        yield()
        future.cancel(/*mayInterruptIfRunning=*/true)
        expect(3)
        latch.countDown()
        deferred.join()
        assertTrue(future.isCancelled)
        assertTrue(deferred.isCancelled)
        assertFailsWith<CancellationException> { future.get() }
        finish(4)
    }

    @Test
    fun testFutureAwaitCancellationPropagatingToDeferredNoInterruption() = runTest {

        val latch = CountDownLatch(1)
        val executor = MoreExecutors.listeningDecorator(ForkJoinPool.commonPool())
        val future = executor.submit(Callable { latch.await(); 42 })
        val deferred = async {
            expect(2)
            future.await()
        }
        expect(1)
        yield()
        future.cancel(/*mayInterruptIfRunning=*/false)
        expect(3)
        latch.countDown()
        deferred.join()
        assertTrue(future.isCancelled)
        assertTrue(deferred.isCancelled)
        assertFailsWith<CancellationException> { future.get() }
        finish(4)
    }

    @Test
    fun testAsListenableFutureCancellationPropagatingToDeferred() = runTest {
        val latch = CountDownLatch(1)
        val executor = MoreExecutors.listeningDecorator(ForkJoinPool.commonPool())
        val future = executor.submit(Callable { latch.await(); 42 })
        val deferred = async {
            expect(2)
            future.await()
        }
        val asListenableFuture = deferred.asListenableFuture()
        expect(1)
        yield()
        asListenableFuture.cancel(/*mayInterruptIfRunning=*/true)
        expect(3)
        latch.countDown()
        deferred.join()
        assertTrue(future.isCancelled)
        assertTrue(deferred.isCancelled)
        assertTrue(asListenableFuture.isCancelled)
        assertFailsWith<CancellationException> { future.get() }
        finish(4)
    }

    @Test
    fun testAsListenableFutureCancellationPropagatingToDeferredNoInterruption() = runTest {
        val latch = CountDownLatch(1)
        val executor = MoreExecutors.listeningDecorator(ForkJoinPool.commonPool())
        val future = executor.submit(Callable { latch.await(); 42 })
        val deferred = async {
            expect(2)
            future.await()
        }
        val asListenableFuture = deferred.asListenableFuture()
        expect(1)
        yield()
        asListenableFuture.cancel(/*mayInterruptIfRunning=*/false)
        expect(3)
        latch.countDown()
        deferred.join()
        assertFailsWith<CancellationException> { asListenableFuture.get() }
        assertTrue(future.isCancelled)
        assertTrue(asListenableFuture.isCancelled)
        assertTrue(deferred.isCancelled)
        assertFailsWith<CancellationException> { future.get() }
        finish(4)
    }

    @Test
    fun testAsListenableFutureCancellationThroughSetFuture() = runTest {
        val latch = CountDownLatch(1)
        val future = SettableFuture.create<Void>()
        val deferred = async {
            expect(2)
            future.await()
        }
        val asListenableFuture = deferred.asListenableFuture()
        expect(1)
        yield()
        future.setFuture(Futures.immediateCancelledFuture())
        expect(3)
        latch.countDown()
        deferred.join()
        assertFailsWith<CancellationException> { asListenableFuture.get() }
        // Future was not interrupted, but also wasn't blocking, so it will be successfully
        // cancelled by its  parent Coroutine.
        assertTrue(future.isCancelled)
        assertTrue(asListenableFuture.isCancelled)
        assertTrue(deferred.isCancelled)
        assertFailsWith<CancellationException> { future.get() }
        finish(4)
    }

    @Test
    @Ignore  // TODO: propagate cancellation before running listeners.
    fun testAsListenableFuturePropagatesCancellationBeforeRunningListeners() = runTest {
        expect(1)
        val deferred = async(context = Dispatchers.Unconfined) {
            try {
                delay(Long.MAX_VALUE)
            } finally {
                expect(3) // Cancelled.
            }
        }
        val asFuture = deferred.asListenableFuture()
        asFuture.addListener(Runnable { expect(4) }, MoreExecutors.directExecutor())
        assertFalse(asFuture.isDone)
        expect(2)
        asFuture.cancel(false)
        assertTrue(asFuture.isDone)
        assertTrue(asFuture.isCancelled)
        assertFailsWith<CancellationException> { deferred.await() }
        finish(5)
    }

    @Test
    fun testFutureCancellation() = runTest {
        val future = awaitFutureWithCancel(true)
        assertTrue(future.isCancelled)
        assertFailsWith<CancellationException> { future.get() }
        finish(4)
    }

    @Test
    fun testAsListenableDeferredCancellationCauseAndMessagePropagate() = runTest {
        val deferred = CompletableDeferred<Int>()
        val inputCancellationException = CancellationException("Foobar")
        inputCancellationException.initCause(OutOfMemoryError("Foobaz"))
        deferred.cancel(inputCancellationException)
        val asFuture = deferred.asListenableFuture()

        val outputCancellationException =
          assertFailsWith<CancellationException> { asFuture.get() }
        val cause = outputCancellationException.cause
        assertNotNull(cause)
        assertEquals(cause.message, "Foobar")
        assertTrue(cause.cause is OutOfMemoryError)
        assertEquals(cause.cause?.message, "Foobaz")
    }

    @Test
    fun testNoFutureCancellation() = runTest {
        val future = awaitFutureWithCancel(false)
        assertFalse(future.isCancelled)
        @Suppress("BlockingMethodInNonBlockingContext")
        assertEquals(42, future.get())
        finish(4)
    }

    @Test
    fun testCancelledDeferredAsListenableFutureAwaitThrowsCancellation() = runTest {
        val future = Futures.immediateCancelledFuture<Int>()
        val asDeferred = future.asDeferred()
        val asDeferredAsFuture = asDeferred.asListenableFuture()

        assertTrue(asDeferredAsFuture.isCancelled)
        assertFailsWith<CancellationException> {
            asDeferredAsFuture.await()
        }
    }

    @Test
    fun testCancelledDeferredAsListenableFutureAsDeferredPassesCancellationAlong() = runTest {
        val deferred = CompletableDeferred<Int>()
        deferred.completeExceptionally(CancellationException())
        val asFuture = deferred.asListenableFuture()
        val asFutureAsDeferred = asFuture.asDeferred()

        assertTrue(asFutureAsDeferred.isCancelled)
        assertTrue(asFutureAsDeferred.isCompleted)
        // By documentation, join() shouldn't throw when asDeferred is already complete.
        asFutureAsDeferred.join()
        assertTrue(asFutureAsDeferred.getCompletionExceptionOrNull() is CancellationException)
    }

    @Test
    fun testCancelledFutureAsDeferredAwaitThrowsCancellation() = runTest {
        val future = Futures.immediateCancelledFuture<Int>()
        val asDeferred = future.asDeferred()

        assertTrue(asDeferred.isCancelled)
        assertFailsWith<CancellationException> {
            asDeferred.await()
        }
    }

    @Test
    fun testCancelledFutureAsDeferredJoinDoesNotThrow() = runTest {
        val future = Futures.immediateCancelledFuture<Int>()
        val asDeferred = future.asDeferred()

        assertTrue(asDeferred.isCancelled)
        assertTrue(asDeferred.isCompleted)
        // By documentation, join() shouldn't throw when asDeferred is already complete.
        asDeferred.join()
        assertTrue(asDeferred.getCompletionExceptionOrNull() is CancellationException)
    }

    @Test
    fun testCompletedFutureAsDeferred() = runTest {
        val future = SettableFuture.create<Int>()
        val task = async {
            expect(2)
            assertEquals(42, future.asDeferred().await())
            expect(4)
        }

        expect(1)
        yield()
        expect(3)
        future.set(42)
        task.join()
        finish(5)
    }

    @Test
    fun testFailedFutureAsDeferred() = runTest {
        val future = SettableFuture.create<Int>().apply {
            setException(TestException())
        }
        val deferred = future.asDeferred()
        assertTrue(deferred.isCancelled && deferred.isCompleted)
        val completionException = deferred.getCompletionExceptionOrNull()!!
        assertTrue(completionException is TestException)

        try {
            deferred.await()
            expectUnreached()
        } catch (e: Throwable) {
            assertTrue(e is TestException)
        }
    }

    @Test
    fun testFutureCompletedWithNullFastPathAsDeferred() = runTest {
        val executor = MoreExecutors.listeningDecorator(ForkJoinPool.commonPool())
        val future = executor.submit(Callable<Int> { null }).also {
            @Suppress("BlockingMethodInNonBlockingContext")
            it.get()
        }
        assertNull(future.asDeferred().await())
    }

    @Test
    fun testFutureCompletedWithNullSlowPathAsDeferred() = runTest {
        val latch = CountDownLatch(1)
        val executor = MoreExecutors.listeningDecorator(ForkJoinPool.commonPool())

        val future = executor.submit(Callable<Int> {
            latch.await()
            null
        })

        val awaiter = async(start = CoroutineStart.UNDISPATCHED) {
            future.asDeferred().await()
        }

        latch.countDown()
        assertNull(awaiter.await())
    }

    @Test
    fun testThrowingFutureAsDeferred() = runTest {
        val executor = MoreExecutors.listeningDecorator(ForkJoinPool.commonPool())
        val future = executor.submit(Callable { throw TestException() })
        try {
            future.asDeferred().await()
            expectUnreached()
        } catch (e: Throwable) {
            assertTrue(e is TestException)
        }
    }

    @Test
    fun testStructuredException() = runTest(
        expected = { it is TestException } // exception propagates to parent with structured concurrency
    ) {
        val result = future<Int>(Dispatchers.Unconfined) {
            throw TestException("FAIL")
        }
        result.checkFutureException<TestException>()
    }

    @Test
    fun testChildException() = runTest(
        expected = { it is TestException } // exception propagates to parent with structured concurrency
    ) {
        val result = future(Dispatchers.Unconfined) {
            // child crashes
            launch { throw TestException("FAIL") }
            42
        }
        result.checkFutureException<TestException>()
    }

    @Test
    fun testExternalCancellation() = runTest {
        val future = future(Dispatchers.Unconfined) {
            try {
                delay(Long.MAX_VALUE)
                expectUnreached()
            } catch (e: CancellationException) {
                expect(2)
                throw e
            }
        }

        yield()
        expect(1)
        future.cancel(true)
        finish(3)
    }

    @Test
    fun testExceptionOnExternalCancellation() = runTest(expected = {it is TestException}) {
        val result = future(Dispatchers.Unconfined) {
            try {
                expect(1)
                delay(Long.MAX_VALUE)
                expectUnreached()
            } catch (e: CancellationException) {
                expect(3)
                throw TestException()
            }
        }
        expect(2)
        result.cancel(true)
        finish(4)
    }

    @Test
    fun testUnhandledExceptionOnExternalCancellation() = runTest(
        unhandled = listOf(
            { it -> it is TestException } // exception is unhandled because there is no parent
        )
    ) {
        expect(1)
        // No parent here (NonCancellable), so nowhere to propagate exception
        val result = future(NonCancellable + Dispatchers.Unconfined) {
            try {
                delay(Long.MAX_VALUE)
            } finally {
                expect(2)
                throw TestException() // this exception cannot be handled
            }
        }
        result.cancel(true)
        finish(3)
    }

    /** This test ensures that we never pass [CancellationException] to [CoroutineExceptionHandler]. */
    @Test
    fun testCancellationExceptionOnExternalCancellation() = runTest {
        expect(1)
        // No parent here (NonCancellable), so nowhere to propagate exception
        val result = future(NonCancellable + Dispatchers.Unconfined) {
            try {
                delay(Long.MAX_VALUE)
            } finally {
                expect(2)
                throw TestCancellationException() // this exception cannot be handled
            }
        }
        assertTrue(result.cancel(true))
        finish(3)
    }

    @Test
    fun testCancellingFutureContextJobCancelsFuture() = runTest {
        expect(1)
        val supervisorJob = SupervisorJob()
        val future = future(context = supervisorJob) {
            expect(2)
            try {
                delay(Long.MAX_VALUE)
                expectUnreached()
            } catch (e: CancellationException) {
                expect(4)
                throw e
            }
        }
        yield()
        expect(3)
        supervisorJob.cancel(CancellationException("Parent cancelled", TestException()))
        supervisorJob.join()
        assertTrue(future.isDone)
        assertTrue(future.isCancelled)
        val thrown = assertFailsWith<CancellationException> { future.get() }
        val cause = thrown.cause
        assertNotNull(cause)
        assertTrue(cause is CancellationException)
        assertEquals("Parent cancelled", cause.message)
        assertTrue(cause.cause is TestException)
        finish(5)
    }

    @Test
    fun testFutureChildException() = runTest {
        val future = future(context = NonCancellable + Dispatchers.Unconfined) {
            val foo = async { delay(Long.MAX_VALUE); 42 }
            val bar = async<Int> { throw TestException() }
            foo.await() + bar.await()
        }
        future.checkFutureException<TestException>()
    }

    @Test
    fun testFutureIsDoneAfterChildrenCompleted() = runTest {
        expect(1)
        val testException = TestException()
        // Don't propagate exception to the test and use different dispatchers as we are going to block test thread.
        val future = future(context = NonCancellable + Dispatchers.Default) {
            val foo = async {
                try {
                    delay(Long.MAX_VALUE)
                    42
                } finally {
                    withContext(NonCancellable) {
                        delay(200)
                    }
                }
            }
            foo.invokeOnCompletion {
                expect(3)
            }
            val bar = async<Int> { throw testException }
            foo.await() + bar.await()
        }
        yield()
        expect(2)
        // Blocking get should succeed after internal coroutine completes.
        val thrown = assertFailsWith<ExecutionException> { future.get() }
        expect(4)
        assertEquals(testException, thrown.cause)
        finish(5)
    }

    @Test
    @Ignore  // TODO: propagate cancellation before running listeners.
    fun testFuturePropagatesCancellationBeforeRunningListeners() = runTest {
        expect(1)
        val future = future(context = Dispatchers.Unconfined) {
            try {
                delay(Long.MAX_VALUE)
            } finally {
                expect(3) // Cancelled.
            }
        }
        future.addListener(Runnable { expect(4) }, MoreExecutors.directExecutor())
        assertFalse(future.isDone)
        expect(2)
        future.cancel(false)
        assertTrue(future.isDone)
        assertTrue(future.isCancelled)
        finish(5)
    }

    private inline fun <reified T: Throwable> ListenableFuture<*>.checkFutureException() {
        val e = assertFailsWith<ExecutionException> { get() }
        val cause = e.cause!!
        assertTrue(cause is T)
    }

    @Suppress("SuspendFunctionOnCoroutineScope")
    private suspend fun CoroutineScope.awaitFutureWithCancel(cancellable: Boolean): ListenableFuture<Int> {
        val latch = CountDownLatch(1)
        val executor = MoreExecutors.listeningDecorator(ForkJoinPool.commonPool())
        val future = executor.submit(Callable { latch.await(); 42 })
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
}
