package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*
import kotlin.test.*

class NonCancellableTest : TestBase() {

    @Test
    fun testNonCancellable() = runTest {
        expect(1)
        val job = async(coroutineContext) {
            withContext(NonCancellable) {
                expect(2)
                yield()
                expect(4)
            }

            expect(5)
            yield()
            expectUnreached()
        }

        yield()
        job.cancel()
        expect(3)
        assertTrue(job.isCancelled)
        try {
            job.await()
            expectUnreached()
        } catch (e: JobCancellationException) {
            assertNull(e.cause)
            finish(6)
        }
    }

    @Test
    fun testNonCancellableWithException() = runTest {
        expect(1)
        val job = async(coroutineContext) {
            withContext(NonCancellable) {
                expect(2)
                yield()
                expect(4)
            }

            expect(5)
            yield()
            expectUnreached()
        }

        yield()
        job.cancel(NumberFormatException())
        expect(3)
        assertTrue(job.isCancelled)
        try {
            job.await()
            expectUnreached()
        } catch (e: JobCancellationException) {
            assertTrue(e.cause is NumberFormatException)
            finish(6)
        }
    }

    @Test
    fun testNonCancellableFinally() = runTest {
        expect(1)
        val job = async(coroutineContext) {
            try {
                expect(2)
                yield()
                expectUnreached()
            } finally {
                withContext(NonCancellable) {
                    expect(4)
                    yield()
                    expect(5)
                }
            }

            expectUnreached()
        }

        yield()
        job.cancel()
        expect(3)
        assertTrue(job.isCancelled)

        try {
            job.await()
            expectUnreached()
        } catch (e: JobCancellationException) {
            finish(6)
        }
    }

    @Test
    fun testNonCancellableTwice() = runTest {
        expect(1)
        val job = async(coroutineContext) {
            withContext(NonCancellable) {
                expect(2)
                yield()
                expect(4)
            }

            withContext(NonCancellable) {
                expect(5)
                yield()
                expect(6)
            }
        }

        yield()
        job.cancel()
        expect(3)
        assertTrue(job.isCancelled)
        try {
            job.await()
            expectUnreached()
        } catch (e: JobCancellationException) {
            assertNull(e.cause)
            finish(7)
        }
    }
}
