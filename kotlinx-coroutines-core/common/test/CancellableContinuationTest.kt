package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*

class CancellableContinuationTest : TestBase() {
    @Test
    fun testResumeWithExceptionAndResumeWithException() = runTest {
        var continuation: Continuation<Unit>? = null
        val job = launch {
            try {
                expect(2)
                suspendCancellableCoroutine { c ->
                    continuation = c
                }
            } catch (_: TestException) {
                expect(3)
            }
        }
        expect(1)
        yield()
        continuation!!.resumeWithException(TestException())
        yield()
        assertFailsWith<IllegalStateException> { continuation.resumeWithException(TestException()) }
        job.join()
        finish(4)
    }

    @Test
    fun testResumeAndResumeWithException() = runTest {
        var continuation: Continuation<Unit>? = null
        val job = launch {
            expect(2)
            suspendCancellableCoroutine { c ->
                continuation = c
            }
            expect(3)
        }
        expect(1)
        yield()
        continuation!!.resume(Unit)
        job.join()
        assertFailsWith<IllegalStateException> { continuation.resumeWithException(TestException()) }
        finish(4)
    }

    @Test
    fun testResumeAndResume() = runTest {
        var continuation: Continuation<Unit>? = null
        val job = launch {
            expect(2)
            suspendCancellableCoroutine { c ->
                continuation = c
            }
            expect(3)
        }
        expect(1)
        yield()
        continuation!!.resume(Unit)
        job.join()
        assertFailsWith<IllegalStateException> { continuation.resume(Unit) }
        finish(4)
    }

    /**
     * Cancelling the outer job may, in practice, race with an attempt to resume continuation and resumes
     * should be ignored. Here suspended coroutine is cancelled but then resumed with exception.
     */
    @Test
    fun testCancelAndResumeWithException() = runTest {
        var continuation: Continuation<Unit>? = null
        val job = launch {
            try {
                expect(2)
                suspendCancellableCoroutine { c ->
                    continuation = c
                }
            } catch (_: CancellationException) {
                expect(3)
            }
        }
        expect(1)
        yield()
        job.cancel() // Cancel job
        yield()
        continuation!!.resumeWithException(TestException()) // Should not fail
        finish(4)
    }

    /**
     * Cancelling outer job may, in practise, race with attempt to resume continuation and resumes
     * should be ignored. Here suspended coroutine is cancelled but then resumed with exception.
     */
    @Test
    fun testCancelAndResume() = runTest {
        var continuation: Continuation<Unit>? = null
        val job = launch {
            try {
                expect(2)
                suspendCancellableCoroutine { c ->
                    continuation = c
                }
            } catch (_: CancellationException) {
                expect(3)
            }
        }
        expect(1)
        yield()
        job.cancel() // Cancel job
        yield()
        continuation!!.resume(Unit) // Should not fail
        finish(4)
    }

    @Test
    fun testCompleteJobWhileSuspended() = runTest {
        expect(1)
        val completableJob = Job()
        val coroutineBlock = suspend {
            assertFailsWith<CancellationException> {
                suspendCancellableCoroutine<Unit> { cont ->
                    expect(2)
                    assertSame(completableJob, cont.context[Job])
                    completableJob.complete()
                }
                expectUnreached()
            }
            expect(3)
        }
        coroutineBlock.startCoroutine(Continuation(completableJob) {
            assertEquals(Unit, it.getOrNull())
            expect(4)
        })
        finish(5)
    }

    /** Tests that the compiler recognizes that [suspendCancellableCoroutine] invokes its block exactly once. */
    @Test
    fun testSuspendCancellableCoroutineContract() = runTest {
        val i: Int
        suspendCancellableCoroutine { cont ->
            i = 1
            cont.resume(Unit)
        }
        assertEquals(1, i)
    }
}
