package kotlinx.coroutines.experimental.exceptions

import kotlinx.coroutines.experimental.*
import org.junit.Test
import java.io.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class JobNestedExceptionsTest : TestBase() {

    @Test
    fun testExceptionUnwrapping() {
        val exception = runBlock {
            val job = Job()
            launch(coroutineContext, parent = job) {
                expect(2)
                launch(coroutineContext) {
                    launch(coroutineContext) {
                        launch(coroutineContext) {
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
            launch(coroutineContext, parent = job) {
                expect(2)
                launch(coroutineContext) {
                    launch(coroutineContext) {
                        launch(coroutineContext) {
                            launch(coroutineContext) {
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
            val job = launch(coroutineContext.minusKey(Job), CoroutineStart.ATOMIC) {
                expect(2)

                launch(coroutineContext, CoroutineStart.ATOMIC) {
                    expect(3)
                    throw IOException()
                }

                throw ArithmeticException()
            }

            job.join()
            finish(4)
        }

        assertTrue(exception is ArithmeticException)
        checkException<IOException>(exception.suppressed()[0])
    }

    @Test
    fun testChildThrowsDuringCompletion() {
        val exceptions = runBlockForMultipleExceptions {
            expect(1)
            val job = launch(coroutineContext.minusKey(Job), CoroutineStart.ATOMIC) {
                expect(2)

                launch(coroutineContext, CoroutineStart.ATOMIC) {
                    expect(3)
                    launch(coroutineContext, CoroutineStart.ATOMIC) {
                        // This child attaches to the parent and throws after parent completion
                        expect(4)
                        throw NullPointerException()
                    }

                    throw IOException()
                }

                throw ArithmeticException()
            }

            job.join()
            finish(5)
        }

        assertEquals(2, exceptions.size)
        assertTrue(exceptions[0] === exceptions[1]) // Sad part about sharing exceptions :(
        val exception = exceptions[0]
        val suppressed = exception.suppressed()
        checkException<IOException>(suppressed[0])
        checkException<NullPointerException>(suppressed[1])
        checkCycles(exception)
    }
}
