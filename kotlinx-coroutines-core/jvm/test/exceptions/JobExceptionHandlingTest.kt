/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import kotlinx.coroutines.CoroutineStart.*
import org.junit.Test
import java.io.*
import kotlin.test.*

@Suppress("DEPRECATION") // cancel(cause)
class JobExceptionHandlingTest : TestBase() {

    @Test
    fun testChildException() {
        /*
         * Root parent: JobImpl()
         * Child: throws ISE
         * Result: ISE in exception handlerWithContextExceptionHandlingTest
         */
        val exception = captureExceptionsRun {
            val job = Job()
            launch(job, start = ATOMIC) {
                expect(2)
                throw IllegalStateException()
            }

            expect(1)
            job.join()
            finish(3)
        }

        checkException<IllegalStateException>(exception)
    }

    @Test
    fun testAsyncCancellationWithCauseAndParent() = runTest {
        val parent = Job()
        val deferred = async(parent) {
            expect(2)
            delay(Long.MAX_VALUE)
        }

        expect(1)
        yield()
        parent.completeExceptionally(IOException())
        try {
            deferred.await()
            expectUnreached()
        } catch (e: CancellationException) {
            assertTrue(e.suppressed.isEmpty())
            assertTrue(e.cause?.suppressed?.isEmpty() ?: false)
            finish(3)
        }
    }

    @Test
    fun testAsyncCancellationWithCauseAndParentDoesNotTriggerHandling() = runTest {
        val parent = Job()
        val job = launch(parent) {
            expect(2)
            delay(Long.MAX_VALUE)
        }

        expect(1)
        yield()
        parent.completeExceptionally(IOException())
        job.join()
        finish(3)
    }

    @Test
    fun testExceptionDuringCancellation() {
        /*
         * Root parent: JobImpl()
         * Launcher: cancels job
         * Child: throws ISE
         * Result: ISE in exception handler
         *
         * Github issue #354
         */
        val exception = captureExceptionsRun {
            val job = Job()
            val child = launch(job, start = ATOMIC) {
                expect(2)
                throw IllegalStateException()
            }

            expect(1)
            job.cancelAndJoin()
            assert(child.isCompleted && !child.isActive)
            finish(3)
        }

        checkException<IllegalStateException>(exception)
    }

    @Test
    fun testExceptionOnChildCancellation() {
        /*
         * Root parent: JobImpl()
         * Child: launch inner child and cancels parent
         * Inner child: throws AE
         * Result: AE in exception handler
         */
        val exception = captureExceptionsRun {
            val job = Job()
            launch(job) {
                expect(2) // <- child is launched successfully

                launch {
                    expect(3) // <- child's child is launched successfully
                    try {
                        yield()
                    } catch (e: CancellationException) {
                        throw ArithmeticException()
                    }
                }

                yield()
                expect(4)
                job.cancel()
            }

            expect(1)
            job.join()
            finish(5)
        }

        checkException<ArithmeticException>(exception)
    }

    @Test
    fun testInnerChildException() {
        /*
        * Root parent: JobImpl()
        * Launcher: launch child and cancel root
        * Child: launch nested child atomically and yields
        * Inner child: throws AE
        * Result: AE
        */
        val exception = captureExceptionsRun {
            val job = Job()
            launch(job, start = ATOMIC) {
                expect(2)
                launch(start = ATOMIC) {
                    expect(3) // <- child's child is launched successfully
                    throw ArithmeticException()
                }

                yield() // will throw cancellation exception
            }

            expect(1)
            job.cancelAndJoin()
            finish(4)
        }

        checkException<ArithmeticException>(exception)
    }

    @Test
    fun testExceptionOnChildCancellationWithCause() {
        /*
         * Root parent: JobImpl()
         * Child: launch inner child and cancels parent with IOE
         * Inner child: throws AE
         * Result: IOE with suppressed AE
         */
        val exception = captureExceptionsRun {
            val job = Job()
            launch(job) {
                expect(2) // <- child is launched successfully
                launch {
                    expect(3) // <- child's child is launched successfully
                    try {
                        yield()
                    } catch (e: CancellationException) {
                        throw ArithmeticException()
                    }
                }

                yield()
                expect(4)
                job.completeExceptionally(IOException())
            }

            expect(1)
            job.join()
            finish(5)
        }

        assertTrue(exception is ArithmeticException)
        assertNull(exception.cause)
        assertTrue(exception.suppressed.isEmpty())
    }

    @Test
    fun testMultipleChildrenThrowAtomically() {
        /*
          * Root parent: JobImpl()
          * Launcher: launches child
          * Child: launch 3 children, each of them throws an exception (AE, IOE, IAE) and calls delay()
          * Result: AE with suppressed IOE and IAE
          */
        val exception = captureExceptionsRun {
            val job = Job()
            launch(job, start = ATOMIC) {
                expect(2)
                launch(start = ATOMIC) {
                    expect(3)
                    throw ArithmeticException()
                }

                launch(start = ATOMIC) {
                    expect(4)
                    throw IOException()
                }

                launch(start = ATOMIC) {
                    expect(5)
                    throw IllegalArgumentException()
                }

                delay(Long.MAX_VALUE)
            }

            expect(1)
            job.join()
            finish(6)
        }

        assertTrue(exception is ArithmeticException)
        val suppressed = exception.suppressed
        assertEquals(2, suppressed.size)
        assertTrue(suppressed[0] is IOException)
        assertTrue(suppressed[1] is IllegalArgumentException)
    }

    @Test
    fun testMultipleChildrenAndParentThrowsAtomic() {
        /*
         * Root parent: JobImpl()
         * Launcher: launches child
         * Child: launch 2 children (each of them throws an exception (IOE, IAE)), throws AE
         * Result: AE with suppressed IOE and IAE
         */
        val exception = captureExceptionsRun {
            val job = Job()
            launch(job, start = ATOMIC) {
                expect(2)
                launch(start = ATOMIC) {
                    expect(3)
                    throw IOException()
                }

                launch(start = ATOMIC) {
                    expect(4)
                    throw IllegalArgumentException()
                }

                throw AssertionError()
            }

            expect(1)
            job.join()
            finish(5)
        }

        assertTrue(exception is AssertionError)
        val suppressed = exception.suppressed
        assertEquals(2, suppressed.size)
        assertTrue(suppressed[0] is IOException)
        assertTrue(suppressed[1] is IllegalArgumentException)
    }

    @Test
    fun testExceptionIsHandledOnce() = runTest(unhandled = listOf { e -> e is TestException }) {
        val job = Job()
        val j1 = launch(job) {
            expect(1)
            delay(Long.MAX_VALUE)
        }

        val j2 = launch(job) {
            expect(2)
            throw TestException()
        }

        joinAll(j1 ,j2)
        finish(3)
    }

    @Test
    fun testCancelledParent() = runTest {
        expect(1)
        val parent = Job()
        parent.completeExceptionally(TestException())
        launch(parent) {
            expectUnreached()
        }.join()
        finish(2)
    }

    @Test
    fun testBadException() = runTest(unhandled = listOf({e -> e is BadException})) {
        val job = launch(Job()) {
            expect(2)
            launch {
                expect(3)
                throw BadException()
            }

            launch(start = CoroutineStart.ATOMIC) {
                expect(4)
                throw BadException()
            }

            yield()
            BadException()
        }

        expect(1)
        yield()
        yield()
        expect(5)
        job.join()
        finish(6)
    }

    private class BadException : Exception() {
        override fun hashCode(): Int {
            throw AssertionError()
        }
    }
}
