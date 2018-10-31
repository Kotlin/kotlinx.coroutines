/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import org.junit.Test
import java.io.*
import kotlin.test.*

class JobNestedExceptionsTest : TestBase() {

    @Test
    fun testExceptionUnwrapping() {
        val exception = runBlock {
            val job = Job()
            launch(job) {
                expect(2)
                launch {
                    launch {
                        launch {
                            throw IllegalStateException()
                        }
                    }
                }
            }

            expect(1)
            job.join()
            finish(3)
        }

        checkException<IllegalStateException>(exception)
        checkCycles(exception)
    }

    @Test
    fun testExceptionUnwrappingWithSuspensions() {
        val exception = runBlock {
            val job = Job()
            launch(job) {
                expect(2)
                launch {
                    launch {
                        launch {
                            launch {
                                throw IOException()
                            }
                            yield()
                        }
                        delay(Long.MAX_VALUE)
                    }
                    delay(Long.MAX_VALUE)
                }
                delay(Long.MAX_VALUE)
            }

            expect(1)
            job.join()
            finish(3)
        }

        assertTrue(exception is IOException)
    }

    @Test
    fun testNestedAtomicThrow() {
        val exception = runBlock {
            expect(1)
            val job = launch(NonCancellable + CoroutineName("outer"), start = CoroutineStart.ATOMIC) {
                expect(2)
                launch(CoroutineName("nested"), start = CoroutineStart.ATOMIC) {
                    expect(4)
                    throw IOException()
                }
                expect(3)
                throw ArithmeticException()
            }
            job.join()
            finish(5)
        }
        assertTrue(exception is ArithmeticException, "Found $exception")
        checkException<IOException>(exception.suppressed[0])
    }

    @Test
    fun testChildThrowsDuringCompletion() {
        val exceptions = runBlockForMultipleExceptions {
            expect(1)
            val job = launch(NonCancellable + CoroutineName("outer"), start = CoroutineStart.ATOMIC) {
                expect(2)
                launch(CoroutineName("nested"), start = CoroutineStart.ATOMIC) {
                    expect(4)
                    launch(CoroutineName("nested2"), start = CoroutineStart.ATOMIC) {
                        // This child attaches to the parent and throws after parent completion
                        expect(6)
                        throw NullPointerException()
                    }
                    expect(5)
                    throw IOException()
                }
                expect(3)
                throw ArithmeticException()
            }

            job.join()
            finish(7)
        }

        assertEquals(1, exceptions.size, "Found $exceptions")
        val exception = exceptions[0]
        assertTrue(exception is ArithmeticException, "Exception is $exception")
        val suppressed = exception.suppressed
        val ioe = suppressed[0]
        assertTrue(ioe is IOException)
        checkException<NullPointerException>(ioe.suppressed[0])
        checkCycles(exception)
    }
}
