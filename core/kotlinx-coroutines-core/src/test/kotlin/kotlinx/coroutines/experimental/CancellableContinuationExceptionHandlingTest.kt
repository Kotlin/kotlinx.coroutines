package kotlinx.coroutines.experimental

import org.junit.Test
import java.io.*
import java.nio.channels.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class CancellableContinuationExceptionHandlingTest : TestBase() {

    @Test
    fun testCancellation() = runTest {
        /*
         * Continuation cancelled without cause
         * Continuation itself throws ISE
         * Result: ISE with suppressed CancellationException
         */
        runCancellation(coroutineContext, null, IllegalStateException()) { e ->
            assertNull(e.cause)
            val suppressed = e.suppressed()
            assertTrue(suppressed.size == 1)

            val cancellation = suppressed[0] as CancellationException
            assertNull(cancellation.cause)
            assertTrue(cancellation.suppressed().isEmpty())
        }
    }

    @Test
    fun testCancellationWithException() = runTest {
        /*
         * Continuation cancelled with IOE
         * Continuation itself throws ISE
         * Result: ISE with suppressed CancellationException(IOE)
         */
        val cancellationCause = IOException()
        runCancellation(coroutineContext, cancellationCause, IllegalStateException()) { e ->
            assertNull(e.cause)
            val suppressed = e.suppressed()
            assertTrue(suppressed.size == 1)

            val cancellation = suppressed[0] as CancellationException
            assertSame(cancellation.cause, cancellationCause)
            assertTrue(cancellationCause.suppressed().isEmpty())
        }
    }

    @Test
    fun testSameException() = runTest {
        /*
         * Continuation cancelled with ISE
         * Continuation itself throws the same ISE
         * Result: ISE
         */
        val cancellationCause = IllegalStateException()
        runCancellation(coroutineContext, cancellationCause, cancellationCause) { e ->
            assertNull(e.cause)
            val suppressed = e.suppressed()
            assertTrue(suppressed.isEmpty())
        }
    }

    @Test
    fun testSameCancellation() = runTest {
        /*
         * Continuation cancelled with CancellationException
         * Continuation itself throws the same CE
         * Result: CE
         */
        val cancellationCause = CancellationException()
        runCancellation(coroutineContext, cancellationCause, cancellationCause) { e ->
            assertNull(e.cause)
            assertSame(e, cancellationCause)
            val suppressed = e.suppressed()
            assertTrue(suppressed.isEmpty())
        }
    }

    @Test
    fun testSameCancellationWithException() = runTest {
        /*
         * Continuation cancelled with CancellationException(IOE)
         * Continuation itself throws the same IOE
         * Result: IOE
         */
        val cancellationCause = CancellationException()
        val exception = IOException()
        cancellationCause.initCause(exception)
        runCancellation(coroutineContext, cancellationCause, exception) { e ->
            assertNull(e.cause)
            assertSame(exception, e)
            assertTrue(e.suppressed().isEmpty())
        }
    }

    @Test
    fun testConflictingCancellation() = runTest {
        /*
         * Continuation cancelled with ISE
         * Continuation itself throws CE(IOE)
         * Result: CE(IOE) with suppressed JCE(ISE)
         */
        val cancellationCause = IllegalStateException()
        val thrown = CancellationException()
        thrown.initCause(IOException())
        runCancellation(coroutineContext, cancellationCause, thrown) { e ->
            assertSame(thrown, e)
            assertEquals(1, thrown.suppressed().size)

            val suppressed = thrown.suppressed()[0]
            assertTrue(suppressed is JobCancellationException)
            assertTrue(suppressed.cause is IllegalStateException)
        }
    }

    @Test
    fun testConflictingCancellation2() = runTest {
        /*
         * Continuation cancelled with ISE
         * Continuation itself throws CE
         * Result: CE with suppressed JCE(ISE)
         */
        val cancellationCause = IllegalStateException()
        val thrown = CancellationException()
        runCancellation(coroutineContext, cancellationCause, thrown) { e ->
            assertSame(thrown, e)
            assertEquals(1, thrown.suppressed().size)

            val suppressed = thrown.suppressed()[0]
            assertTrue(suppressed is JobCancellationException)
            assertTrue(suppressed.cause is IllegalStateException)

        }
    }

    @Test
    fun testConflictingCancellation3() = runTest {
        /*
         * Continuation cancelled with CE
         * Continuation itself throws CE
         * Result: CE
         */
        val cancellationCause = CancellationException()
        val thrown = CancellationException()
        runCancellation(coroutineContext, cancellationCause, thrown) { e ->
            assertSame(thrown, e)
            assertNull(e.cause)
            assertTrue(e.suppressed().isEmpty())
        }
    }

    @Test
    fun testConflictingCancellationWithSameException() = runTest {
        val cancellationCause = IllegalStateException()
        val thrown = CancellationException()
        /*
         * Continuation cancelled with ISE
         * Continuation itself throws CE with the same ISE as a cause
         * Result: CE(ISE)
         */
        thrown.initCause(cancellationCause)
        runCancellation(coroutineContext, cancellationCause, thrown) { e ->
            assertSame(thrown, e)
            assertSame(cancellationCause, e.cause)
            assertEquals(0, thrown.suppressed().size)

        }
    }

    @Test
    fun testThrowingCancellation() = runTest {
        val thrown = CancellationException()
        runThrowingContinuation(coroutineContext, thrown) { e ->
            assertSame(thrown, e)
        }
    }

    @Test
    fun testThrowingCancellationWithCause() = runTest {
        val thrown = CancellationException()
        thrown.initCause(IOException())
        runThrowingContinuation(coroutineContext, thrown) { e ->
            assertSame(thrown, e)
        }
    }

    @Test
    fun testCancel() = runTest {
        runOnlyCancellation(coroutineContext, null) { e ->
            assertNull(e.cause)
            assertTrue(e.suppressed().isEmpty())
        }
    }

    @Test
    fun testCancelWithCause() = runTest {
        val cause = IOException()
        runOnlyCancellation(coroutineContext, cause) { e ->
            assertSame(cause, e.cause)
            assertTrue(e.suppressed().isEmpty())
        }
    }

    @Test
    fun testCancelWithCancellationException() = runTest {
        val cause = CancellationException()
        runThrowingContinuation(coroutineContext, cause) { e ->
            assertSame(cause, e)
            assertNull(e.cause)
            assertTrue(e.suppressed().isEmpty())
        }
    }

    @Test
    fun testMultipleCancellations() = runTest {
        var continuation: Continuation<Unit>? = null

        val job = launch(coroutineContext) {
            try {
                expect(2)
                suspendCancellableCoroutine<Unit> { c ->
                    continuation = c
                }
            } catch (e: IOException) {
                expect(3)
            }
        }

        expect(1)
        yield()
        continuation!!.resumeWithException(IOException())
        yield()
        assertFailsWith<IllegalStateException> { continuation!!.resumeWithException(ClosedChannelException()) }
        try {
            job.join()
        } finally {
            finish(4)
        }
    }

    @Test
    fun testResumeAndCancel() = runTest {
        var continuation: Continuation<Unit>? = null

        val job = launch(coroutineContext) {
            expect(2)
            suspendCancellableCoroutine<Unit> { c ->
                continuation = c
            }
            expect(3)
        }

        expect(1)
        yield()
        continuation!!.resume(Unit)
        job.join()
        assertFailsWith<IllegalStateException> { continuation!!.resumeWithException(ClosedChannelException()) }
        finish(4)
    }

    private fun wrapperDispatcher(context: CoroutineContext): CoroutineContext {
        val dispatcher = context[ContinuationInterceptor] as CoroutineDispatcher
        return object : CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                dispatcher.dispatch(context, block)
            }
        }
    }

    private suspend inline fun <reified T : Exception> CoroutineScope.runCancellation(
        coroutineContext: CoroutineContext,
        cancellationCause: Exception?,
        thrownException: T, exceptionChecker: (T) -> Unit
    ) {

        expect(1)
        val job = Job()
        job.cancel(cancellationCause)

        try {
            withContext(wrapperDispatcher(coroutineContext) + job, CoroutineStart.ATOMIC) {
                require(isActive)
                expect(2)
                throw thrownException
            }
        } catch (e: Exception) {
            assertTrue(e is T)
            exceptionChecker(e as T)
            finish(3)
            return
        }

        fail()
    }

    private suspend inline fun <reified T : Exception> CoroutineScope.runThrowingContinuation(
        coroutineContext: CoroutineContext,
        thrownException: T, exceptionChecker: (T) -> Unit
    ) {

        expect(1)
        try {
            withContext(wrapperDispatcher(coroutineContext), CoroutineStart.ATOMIC) {
                require(isActive)
                expect(2)
                throw thrownException
            }
        } catch (e: Exception) {
            assertTrue(e is T)
            exceptionChecker(e as T)
            finish(3)
            return
        }

        fail()
    }

    private suspend inline fun CoroutineScope.runOnlyCancellation(
        coroutineContext: CoroutineContext,
        cancellationCause: Exception?, exceptionChecker: (CancellationException) -> Unit
    ) {

        expect(1)
        val job = Job()
        job.cancel(cancellationCause)
        try {
            withContext(wrapperDispatcher(coroutineContext) + job, CoroutineStart.ATOMIC) {
                require(isActive)
                expect(2)
            }
        } catch (e: Exception) {
            assertTrue(e is CancellationException)
            exceptionChecker(e as CancellationException)
            finish(3)
            return
        }

        fail()
    }
}

// Workaround to run tests on JDK 8, this test is excluded from jdk16Test task
fun Throwable.suppressed(): Array<Throwable> {
    val method = this::class.java.getMethod("getSuppressed") ?: error("This test can only be run using JDK 1.8")
    return method.invoke(this) as Array<Throwable>
}
