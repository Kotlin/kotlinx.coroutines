package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.Test
import kotlin.test.*

class ProduceExceptionsTest : TestBase() {

    @Test
    fun testFailingProduce() = runTest(unhandled = listOf({ e -> e is TestException })) {
        expect(1)
        val producer = produce<Int>(Job()) {
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

    @Test
    fun testSuppressedExceptionUncaught() =
        runTest(unhandled = listOf({ e -> e is TestException && e.suppressed[0] is TestException2 })) {
            val produce = produce<Int>(Job()) {
                launch(start = CoroutineStart.ATOMIC) {
                    throw TestException()
                }
                try {
                    delay(Long.MAX_VALUE)
                } finally {
                    throw TestException2()
                }
            }

            yield()
            produce.cancel()
        }

    @Test
    fun testSuppressedException() = runTest {
        val produce = produce<Int>(NonCancellable) {
            launch(start = CoroutineStart.ATOMIC) {
                throw TestException() // child coroutine fails
            }
            try {
                delay(Long.MAX_VALUE)
            } finally {
                throw TestException2() // but parent throws another exception while cleaning up
            }
        }
        try {
            produce.receive()
            expectUnreached()
        } catch (e: TestException) {
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
        try {
            channel.receive()
        } catch (e: CancellationException) {
            assertTrue(e.suppressed.isEmpty())
            finish(4)
        }
    }

    @Test
    fun testCancelProduceChannelWithException() = runTest {
        var channel: ReceiveChannel<Int>? = null
        channel = produce(NonCancellable) {
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
        try {
            channel.receive()
        } catch (e: TestCancellationException) {
            assertTrue(e.suppressed.isEmpty())
            finish(4)
        }
    }

    @Test
    fun testCancelChannelWithJob() = runTest {
        val job = Job()
        val channel = produce(job) {
            expect(2)
            job.cancel()
            try {
                send(1)
            } catch (e: CancellationException) {
                expect(3)
                throw e
            }
        }

        expect(1)
        yield()
        try {
            channel.receive()
        } catch (e: CancellationException) {
            assertTrue(e.suppressed.isEmpty())
            finish(4)
        }
    }

    @Test
    fun testCancelChannelWithJobWithException() = runTest {
        val job = Job()
        val channel = produce(job) {
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
        try {
            channel.receive()
        } catch (e: CancellationException) {
            // RECOVER_STACK_TRACES
            assertIs<TestException2>(e.cause?.cause)
            finish(4)
        }
    }
}
