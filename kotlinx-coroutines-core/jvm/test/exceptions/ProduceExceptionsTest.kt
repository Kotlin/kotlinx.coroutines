package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.testing.*
import kotlin.test.*

class ProduceExceptionsTest : TestBase() {

    @Test
    fun testFailingProduce() = runTest(unhandled = listOf({ e -> e is TestException })) {
        // TODO: document this behavior!
        expect(1)
        supervisorScope {
            val producer = produce<Int> {
                expect(2)
                try {
                    yield()
                } finally {
                    expect(3)
                    throw TestException()
                }
            }

            yield()
            producer.cancel()
            yield()
            finish(4)
        }
    }

    @Test
    fun testSuppressedExceptionUncaught() =
        runTest(unhandled = listOf({ e -> e is TestException && e.suppressed[0] is TestException2 })) {
            supervisorScope {
                val produce = produce<Int> {
                    launch(start = CoroutineStart.ATOMIC) {
                        throw TestException()
                    }
                    try {
                        awaitCancellation()
                    } finally {
                        throw TestException2()
                    }
                }

                yield()
                produce.cancel()
            }
        }

    @Test
    fun testSuppressedException() = runTest {
        supervisorScope {
            val produce = produce<Int> {
                launch(start = CoroutineStart.ATOMIC) {
                    throw TestException() // child coroutine fails
                }
                try {
                    awaitCancellation()
                } finally {
                    throw TestException2() // but parent throws another exception while cleaning up
                }
            }
            val e = assertFailsWith<TestException> { produce.receive() }
            assertIs<TestException2>(e.suppressed[0])
        }
    }

    @Test
    fun testCancelProduceChannel() = runTest {
        var channel: ReceiveChannel<Int>? = null
        channel = produce {
            expect(2)
            channel!!.cancel()
            try {
                send(1)
            } catch (e: CancellationException) {
                expect(3)
                throw e
            }
        }

        expect(1)
        yield()
        val e = assertFailsWith<CancellationException> { channel.receive() }
        assertTrue(e.suppressed.isEmpty())
        finish(4)
    }

    @Test
    fun testCancelProduceChannelWithException() = runTest {
        supervisorScope {
            var channel: ReceiveChannel<Int>? = null
            channel = produce {
                expect(2)
                channel!!.cancel(TestCancellationException())
                try {
                    send(1)
                    // Not a ClosedForSendException
                } catch (e: TestCancellationException) {
                    expect(3)
                    throw e
                }
            }

            expect(1)
            yield()
            val e = assertFailsWith<TestCancellationException> { channel.receive() }
            assertTrue(e.suppressed.isEmpty())
            finish(4)
        }
    }

    @Test
    fun testCancelChannelWithJob() = runTest {
        val detachedScope = CoroutineScope(currentCoroutineContext() + Job())
        val channel = detachedScope.produce {
            expect(2)
            detachedScope.cancel()
            try {
                send(1)
            } catch (e: CancellationException) {
                expect(3)
                throw e
            }
        }

        expect(1)
        yield()
        val e = assertFailsWith<CancellationException> { channel.receive() }
        assertTrue(e.suppressed.isEmpty())
        finish(4)
    }

    @Test
    fun testCancelChannelWithJobWithException() = runTest {
        val job = Job()
        val detachedScope = CoroutineScope(currentCoroutineContext() + job)
        val channel = detachedScope.produce {
            expect(2)
            job.completeExceptionally(TestException2())
            try {
                send(1)
            } catch (e: CancellationException) { // Not a TestException2
                expect(3)
                throw e
            }
        }

        expect(1)
        yield()
        val e = assertFailsWith<CancellationException> { channel.receive() }
        // RECOVER_STACK_TRACES
        assertIs<TestException2>(e.cause?.cause)
        finish(4)
    }
}
