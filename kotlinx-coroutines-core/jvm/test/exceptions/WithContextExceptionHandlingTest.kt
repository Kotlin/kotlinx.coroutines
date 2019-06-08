/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import kotlin.coroutines.*
import kotlin.test.*

@RunWith(Parameterized::class)
class WithContextExceptionHandlingTest(private val mode: Mode) : TestBase() {
    enum class Mode { WITH_CONTEXT, ASYNC_AWAIT }

    companion object {
        @Parameterized.Parameters(name = "mode={0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = Mode.values().map { arrayOf<Any>(it) }
    }

    @Test
    fun testCancellation() = runTest {
        /*
         * context cancelled without cause
         * code itself throws TE2
         * Result: TE2
         */
        runCancellation(null, TestException2()) { e ->
            assertTrue(e is TestException2)
            assertNull(e.cause)
            val suppressed = e.suppressed
            assertTrue(suppressed.isEmpty())
        }
    }

    @Test
    fun testCancellationWithException() = runTest {
        /*
         * context cancelled with TCE
         * block itself throws TE2
         * Result: TE (CancellationException is always ignored)
         */
        val cancellationCause = TestCancellationException()
        runCancellation(cancellationCause, TestException2()) { e ->
            assertTrue(e is TestException2)
            assertNull(e.cause)
            val suppressed = e.suppressed
            assertTrue(suppressed.isEmpty())
        }
    }

    @Test
    fun testSameException() = runTest {
        /*
         * context cancelled with TCE
         * block itself throws the same TCE
         * Result: TCE
         */
        val cancellationCause = TestCancellationException()
        runCancellation(cancellationCause, cancellationCause) { e ->
            assertTrue(e is TestCancellationException)
            assertNull(e.cause)
            val suppressed = e.suppressed
            assertTrue(suppressed.isEmpty())
        }
    }

    @Test
    fun testSameCancellation() = runTest {
        /*
         * context cancelled with TestCancellationException
         * block itself throws the same TCE
         * Result: TCE
         */
        val cancellationCause = TestCancellationException()
        runCancellation(cancellationCause, cancellationCause) { e ->
            assertSame(e, cancellationCause)
            assertNull(e.cause)
            val suppressed = e.suppressed
            assertTrue(suppressed.isEmpty())
        }
    }

    @Test
    fun testSameCancellationWithException() = runTest {
        /*
         * context cancelled with CancellationException(TE)
         * block itself throws the same TE
         * Result: TE
         */
        val cancellationCause = CancellationException()
        val exception = TestException()
        cancellationCause.initCause(exception)
        runCancellation(cancellationCause, exception) { e ->
            assertSame(exception, e)
            assertNull(e.cause)
            assertTrue(e.suppressed.isEmpty())
        }
    }

    @Test
    fun testConflictingCancellation() = runTest {
        /*
         * context cancelled with TCE
         * block itself throws CE(TE)
         * Result: TE (because cancellation exception is always ignored and not handled)
         */
        val cancellationCause = TestCancellationException()
        val thrown = CancellationException()
        thrown.initCause(TestException())
        runCancellation(cancellationCause, thrown) { e ->
            assertSame(cancellationCause, e)
            assertTrue(e.suppressed.isEmpty())
        }
    }

    @Test
    fun testConflictingCancellation2() = runTest {
        /*
         * context cancelled with TE
         * block itself throws CE
         * Result: TE
         */
        val cancellationCause = TestCancellationException()
        val thrown = CancellationException()
        runCancellation(cancellationCause, thrown) { e ->
            assertSame(cancellationCause, e)
            val suppressed = e.suppressed
            assertTrue(suppressed.isEmpty())
        }
    }

    @Test
    fun testConflictingCancellation3() = runTest {
        /*
         * context cancelled with TCE
         * block itself throws TCE
         * Result: TCE
         */
        val cancellationCause = TestCancellationException()
        val thrown = TestCancellationException()
        runCancellation(cancellationCause, thrown) { e ->
            assertSame(cancellationCause, e)
            assertNull(e.cause)
            assertTrue(e.suppressed.isEmpty())
        }
    }

    @Test
    fun testThrowingCancellation() = runTest {
        val thrown = TestCancellationException()
        runThrowing(thrown) { e ->
            assertSame(thrown, e)
        }
    }

    @Test
    fun testThrowingCancellationWithCause() = runTest {
        // Exception are never unwrapped, so if CE(TE) is thrown then it is the cancellation cause
        val thrown = TestCancellationException()
        thrown.initCause(TestException())
        runThrowing(thrown) { e ->
           assertSame(thrown, e)
        }
    }

    @Test
    fun testCancel() = runTest {
        runOnlyCancellation(null) { e ->
            val cause = e.cause as JobCancellationException // shall be recovered JCE
            assertNull(cause.cause)
            assertTrue(e.suppressed.isEmpty())
            assertTrue(cause.suppressed.isEmpty())
        }
    }

    @Test
    fun testCancelWithCause() = runTest {
        val cause = TestCancellationException()
        runOnlyCancellation(cause) { e ->
            assertSame(cause, e)
            assertTrue(e.suppressed.isEmpty())
        }
    }

    @Test
    fun testCancelWithCancellationException() = runTest {
        val cause = TestCancellationException()
        runThrowing(cause) { e ->
            assertSame(cause, e)
            assertNull(e.cause)
            assertTrue(e.suppressed.isEmpty())
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
        cancellationCause: CancellationException?,
        thrownException: Throwable,
        exceptionChecker: (Throwable) -> Unit
    ) {
        expect(1)

        try {
            withCtx(wrapperDispatcher(coroutineContext)) { job ->
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
            withCtx(wrapperDispatcher(coroutineContext).minusKey(Job)) {
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

    private suspend fun withCtx(context: CoroutineContext, job: Job = Job(), block: suspend CoroutineScope.(Job) -> Nothing) {
        when (mode) {
            Mode.WITH_CONTEXT -> withContext(context + job) {
                block(job)
            }
            Mode.ASYNC_AWAIT -> CoroutineScope(coroutineContext).async(context + job) {
                block(job)
            }.await()
        }
    }

    private suspend fun runOnlyCancellation(
        cancellationCause: CancellationException?,
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