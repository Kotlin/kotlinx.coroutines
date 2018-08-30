/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.exceptions

import kotlinx.coroutines.experimental.*
import org.junit.Test
import java.io.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class WithContextExceptionHandlingTest : TestBase() {
    @Test
    fun testCancellation() = runTest {
        /*
         * Continuation cancelled without cause
         * Continuation itself throws ISE
         * Result: ISE with suppressed CancellationException
         */
        runCancellation(null, IllegalStateException()) { e ->
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
        runCancellation(cancellationCause, IllegalStateException()) { e ->
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
        runCancellation(cancellationCause, cancellationCause) { e ->
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
        runCancellation(cancellationCause, cancellationCause) { e ->
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
        runCancellation(cancellationCause, exception) { e ->
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
        runCancellation(cancellationCause, thrown) { e ->
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
        runCancellation(cancellationCause, thrown) { e ->
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
        runCancellation(cancellationCause, thrown) { e ->
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
        runCancellation(cancellationCause, thrown) { e ->
            assertSame(thrown, e)
            assertSame(cancellationCause, e.cause)
            assertEquals(0, thrown.suppressed().size)

        }
    }

    @Test
    fun testThrowingCancellation() = runTest {
        val thrown = CancellationException()
        runThrowing(thrown) { e ->
            assertSame(thrown, e)
        }
    }

    @Test
    fun testThrowingCancellationWithCause() = runTest {
        val thrown = CancellationException()
        thrown.initCause(IOException())
        runThrowing(thrown) { e ->
            assertSame(thrown, e)
        }
    }

    @Test
    fun testCancel() = runTest {
        runOnlyCancellation(null) { e ->
            assertNull(e.cause)
            assertTrue(e.suppressed().isEmpty())
        }
    }

    @Test
    fun testCancelWithCause() = runTest {
        val cause = IOException()
        runOnlyCancellation(cause) { e ->
            assertSame(cause, e.cause)
            assertTrue(e.suppressed().isEmpty())
        }
    }

    @Test
    fun testCancelWithCancellationException() = runTest {
        val cause = CancellationException()
        runThrowing(cause) { e ->
            assertSame(cause, e)
            assertNull(e.cause)
            assertTrue(e.suppressed().isEmpty())
        }
    }

    private fun wrapperDispatcher(context: CoroutineContext): CoroutineContext {
        val dispatcher = context[ContinuationInterceptor] as CoroutineDispatcher
        return object : CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                dispatcher.dispatch(context, block)
            }
        }
    }

    private suspend inline fun <reified T : Exception> runCancellation(
        cancellationCause: Exception?,
        thrownException: T,
        exceptionChecker: (T) -> Unit
    ) {
        expect(1)
        val job = Job()
        job.cancel(cancellationCause)
        try {
            withContext(wrapperDispatcher(coroutineContext) + job, CoroutineStart.ATOMIC) {
                require(!isActive) // already cancelled
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

    private suspend inline fun <reified T : Exception> runThrowing(
        thrownException: T,
        exceptionChecker: (T) -> Unit
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

    private suspend inline fun runOnlyCancellation(
        cancellationCause: Exception?,
        exceptionChecker: (CancellationException) -> Unit
    ) {
        expect(1)
        val job = Job()
        job.cancel(cancellationCause)
        try {
            withContext(wrapperDispatcher(coroutineContext) + job, CoroutineStart.ATOMIC) {
                require(!isActive) // is already cancelled
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