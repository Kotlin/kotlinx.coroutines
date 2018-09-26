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
         * context cancelled without cause
         * code itself throws ISE
         * Result: ISE
         */
        runCancellation(null, IllegalStateException()) { e ->
            assertTrue(e is IllegalStateException)
            assertNull(e.cause)
            val suppressed = e.suppressed()
            assertTrue(suppressed.isEmpty())
        }
    }

    @Test
    fun testCancellationWithException() = runTest {
        /*
         * context cancelled with IOE
         * block itself throws ISE
         * Result: IOE with suppressed ISE
         */
        val cancellationCause = IOException()
        runCancellation(cancellationCause, IllegalStateException()) { e ->
            assertTrue(e is IOException)
            assertNull(e.cause)
            val suppressed = e.suppressed()
            assertEquals(suppressed.size, 1)
            assertTrue(suppressed[0] is IllegalStateException)
        }
    }

    @Test
    fun testSameException() = runTest {
        /*
         * context cancelled with ISE
         * block itself throws the same ISE
         * Result: ISE
         */
        val cancellationCause = IllegalStateException()
        runCancellation(cancellationCause, cancellationCause) { e ->
            assertTrue(e is IllegalStateException)
            assertNull(e.cause)
            val suppressed = e.suppressed()
            assertTrue(suppressed.isEmpty())
        }
    }

    @Test
    fun testSameCancellation() = runTest {
        /*
         * context cancelled with CancellationException
         * block itself throws the same CE
         * Result: CE
         */
        val cancellationCause = CancellationException()
        runCancellation(cancellationCause, cancellationCause) { e ->
            assertSame(e, cancellationCause)
            assertNull(e.cause)
            val suppressed = e.suppressed()
            assertTrue(suppressed.isEmpty())
        }
    }

    @Test
    fun testSameCancellationWithException() = runTest {
        /*
         * context cancelled with CancellationException(IOE)
         * block itself throws the same IOE
         * Result: IOE
         */
        val cancellationCause = CancellationException()
        val exception = IOException()
        cancellationCause.initCause(exception)
        runCancellation(cancellationCause, exception) { e ->
            assertSame(exception, e)
            assertNull(e.cause)
            assertTrue(e.suppressed().isEmpty())
        }
    }

    @Test
    fun testConflictingCancellation() = runTest {
        /*
         * context cancelled with ISE
         * block itself throws CE(IOE)
         * Result: ISE suppressed IOE
         */
        val cancellationCause = IllegalStateException()
        val thrown = CancellationException()
        thrown.initCause(IOException())
        runCancellation(cancellationCause, thrown) { e ->
            assertSame(cancellationCause, e)
            val suppressed = e.suppressed()
            assertEquals(1, suppressed.size)
            assertTrue(suppressed[0] is IOException)
        }
    }

    @Test
    fun testConflictingCancellation2() = runTest {
        /*
         * context cancelled with ISE
         * block itself throws CE
         * Result: ISE
         */
        val cancellationCause = IllegalStateException()
        val thrown = CancellationException()
        runCancellation(cancellationCause, thrown) { e ->
            assertSame(cancellationCause, e)
            val suppressed = e.suppressed()
            assertTrue(suppressed.isEmpty())
        }
    }

    @Test
    fun testConflictingCancellation3() = runTest {
        /*
         * context cancelled with CE
         * block itself throws CE
         * Result: CE
         */
        val cancellationCause = CancellationException()
        val thrown = CancellationException()
        runCancellation(cancellationCause, thrown) { e ->
            assertSame(cancellationCause, e)
            assertNull(e.cause)
            assertTrue(e.suppressed().isEmpty())
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
    @Ignore // todo: decide shall we fix unwrapping logic in JobSupport
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
            assertSame(cause, e)
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

    private suspend fun runCancellation(
        cancellationCause: Exception?,
        thrownException: Throwable,
        exceptionChecker: (Throwable) -> Unit
    ) {
        expect(1)
        val job = Job()
        try {
            withContext(wrapperDispatcher(coroutineContext) + job) {
                require(isActive) // not cancelled yet
                job.cancel(cancellationCause)
                require(!isActive) // now cancelled
                expect(2)
                throw thrownException
            }
        } catch (e: Throwable) {
            exceptionChecker(e)
            finish(3)
            return
        }
        fail()
    }

    private suspend fun runThrowing(
        thrownException: Throwable,
        exceptionChecker: (Throwable) -> Unit
    ) {
        expect(1)
        try {
            withContext(wrapperDispatcher(coroutineContext)) {
                require(isActive)
                expect(2)
                throw thrownException
            }
        } catch (e: Throwable) {
            exceptionChecker(e)
            finish(3)
            return
        }
        fail()
    }

    private suspend fun runOnlyCancellation(
        cancellationCause: Throwable?,
        exceptionChecker: (Throwable) -> Unit
    ) {
        expect(1)
        val job = Job()
        try {
            withContext(wrapperDispatcher(coroutineContext) + job) {
                require(isActive) // still active
                job.cancel(cancellationCause)
                require(!isActive) // is already cancelled
                expect(2)
            }
        } catch (e: Throwable) {
            exceptionChecker(e)
            finish(3)
            return
        }
        fail()
    }
}