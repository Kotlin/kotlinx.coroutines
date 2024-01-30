package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.testing.exceptions.*
import org.junit.Test
import java.io.*
import kotlin.test.*

class JobNestedExceptionsTest : TestBase() {

    @Test
    fun testExceptionUnwrapping() {
        val exception = captureExceptionsRun {
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
        val exception = captureExceptionsRun {
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

        assertIs<IOException>(exception)
    }

    @Test
    fun testNestedAtomicThrow() {
        val exception = captureExceptionsRun {
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
        assertIs<ArithmeticException>(exception, "Found $exception")
        checkException<IOException>(exception.suppressed[0])
    }

    @Test
    fun testChildThrowsDuringCompletion() {
        val exception = captureExceptionsRun {
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

        assertIs<ArithmeticException>(exception, "Exception is $exception")
        val suppressed = exception.suppressed
        val ioe = suppressed[0]
        assertIs<IOException>(ioe)
        checkException<NullPointerException>(ioe.suppressed[0])
        checkCycles(exception)
    }
}
