
/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-22237

package kotlinx.coroutines

import kotlin.test.*

class WithContextTest : TestBase() {

    @Test
    fun testThrowException() = runTest {
        expect(1)
        try {
            withContext(coroutineContext) {
                expect(2)
                throw AssertionError()
            }
        } catch (e: AssertionError) {
            expect(3)
        }

        yield()
        finish(4)
    }

    @Test
    fun testThrowExceptionFromWrappedContext() = runTest {
        expect(1)
        try {
            withContext(wrapperDispatcher(coroutineContext)) {
                expect(2)
                throw AssertionError()
            }
        } catch (e: AssertionError) {
            expect(3)
        }

        yield()
        finish(4)
    }

    @Test
    fun testSameContextNoSuspend() = runTest {
        expect(1)
        launch(coroutineContext) { // make sure there is not early dispatch here
            finish(5) // after main exits
        }
        expect(2)
        val result = withContext(coroutineContext) { // same context!
            expect(3) // still here
            "OK".wrap()
        }.unwrap()
        assertEquals("OK", result)
        expect(4)
        // will wait for the first coroutine
    }

    @Test
    fun testSameContextWithSuspend() = runTest {
        expect(1)
        launch(coroutineContext) { // make sure there is not early dispatch here
            expect(4)
        }
        expect(2)
        val result = withContext(coroutineContext) { // same context!
            expect(3) // still here
            yield() // now yields to launch!
            expect(5)
            "OK".wrap()
        }.unwrap()
        assertEquals("OK", result)
        finish(6)
    }

    @Test
    fun testCancelWithJobNoSuspend() = runTest {
        expect(1)
        launch(coroutineContext) { // make sure there is not early dispatch to here
            finish(6) // after main exits
        }
        expect(2)
        val job = Job()
        try {
            withContext(coroutineContext + job) {
                // same context + new job
                expect(3) // still here
                job.cancel() // cancel out job!
                try {
                    yield() // shall throw CancellationException
                    expectUnreached()
                } catch (e: CancellationException) {
                    expect(4)
                }
                "OK".wrap()
            }

            expectUnreached()
        } catch (e: CancellationException) {
            expect(5)
            // will wait for the first coroutine
        }
    }

    @Test
    fun testCancelWithJobWithSuspend() = runTest(
        expected = { it is CancellationException }
    ) {
        expect(1)
        launch(coroutineContext) { // make sure there is not early dispatch to here
            expect(4)
        }
        expect(2)
        val job = Job()
        withContext(coroutineContext + job) { // same context + new job
            expect(3) // still here
            yield() // now yields to launch!
            expect(5)
            job.cancel() // cancel out job!
            try {
                yield() // shall throw CancellationException
                expectUnreached()
            } catch (e: CancellationException) {
                finish(6)
            }
            "OK".wrap()
        }
        // still fails, because parent job was cancelled
        expectUnreached()
    }

    @Test
    fun testRunCancellableDefault() = runTest(
        expected = { it is CancellationException }
    ) {
        val job = Job()
        job.cancel() // cancel before it has a chance to run
        withContext(job + wrapperDispatcher(coroutineContext)) {
            expectUnreached() // will get cancelled
        }
    }

    @Test
    fun testRunCancellationUndispatchedVsException() = runTest {
        expect(1)
        var job: Job? = null
        job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                // Same dispatcher, different context
                withContext(CoroutineName("testRunCancellationUndispatchedVsException")) {
                    expect(3)
                    yield() // must suspend
                    expect(5)
                    job!!.cancel() // cancel this job _before_ it throws
                    throw TestException()
                }
            } catch (e: TestException) {
                // must have caught TextException
                expect(6)
            }
        }
        expect(4)
        yield() // to coroutineScope
        finish(7)
    }

    @Test
    fun testRunCancellationDispatchedVsException() = runTest {
        expect(1)
        var job: Job? = null
        job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                // "Different" dispatcher (schedules execution back and forth)
                withContext(wrapperDispatcher(coroutineContext)) {
                    expect(4)
                    yield() // must suspend
                    expect(6)
                    job!!.cancel() // cancel this job _before_ it throws
                    throw TestException()
                }
            } catch (e: TestException) {
                // must have caught TextException
                expect(8)
            }
        }
        expect(3)
        yield() // withContext is next
        expect(5)
        yield() // withContext again
        expect(7)
        yield() // to catch block
        finish(9)
    }

    @Test
    fun testRunSelfCancellationWithException() = runTest(unhandled = listOf({e -> e is AssertionError})) {
        expect(1)
        var job: Job? = null
        job = launch(Job()) {
            try {
                expect(3)
                withContext(wrapperDispatcher(coroutineContext)) {
                    require(isActive)
                    expect(5)
                    job!!.cancel()
                    require(job!!.cancel(AssertionError())) // cancel again, no success here
                    require(!isActive)
                    throw TestException() // but throw a different exception
                }
            } catch (e: Throwable) {
                expect(7)
                // make sure TestException, not CancellationException or AssertionError is thrown
                assertTrue(e is TestException, "Caught $e")
            }
        }
        expect(2)
        yield() // to the launched job
        expect(4)
        yield() // again to the job
        expect(6)
        yield() // again to exception handler
        finish(8)
    }

    @Test
    fun testRunSelfCancellation() = runTest(unhandled = listOf({e -> e is AssertionError})) {
        expect(1)
        var job: Job? = null
        job = launch(Job()) {
            try {
                expect(3)
                withContext(wrapperDispatcher(coroutineContext)) {
                    require(isActive)
                    expect(5)
                    job!!.cancel() // cancel itself
                    require(job!!.cancel(AssertionError()))
                    require(!isActive)
                    "OK".wrap()
                }
                expectUnreached()
            } catch (e: Throwable) {
                expect(7)
                // make sure JCE is thrown
                assertTrue(e is CancellationException, "Caught $e")
            }
        }

        expect(2)
        yield() // to the launched job
        expect(4)
        yield() // again to the job
        expect(6)
        yield() // again to exception handler
        finish(8)
    }

    @Test
    fun testWithContextScopeFailure() = runTest {
        expect(1)
        try {
            withContext(wrapperDispatcher(coroutineContext)) {
                expect(2)
                // launch a child that fails
                launch {
                    expect(4)
                    throw TestException()
                }
                expect(3)
                "OK".wrap()
            }
            expectUnreached()
        } catch (e: TestException) {
            // ensure that we can catch exception outside of the scope
            expect(5)
        }
        finish(6)
    }

    @Test
    fun testWithContextChildWaitSameContext() = runTest {
        expect(1)
        withContext(coroutineContext) {
            expect(2)
            launch {
                // ^^^ schedules to main thread
                expect(4) // waits before return
            }
            expect(3)
            "OK".wrap()
        }.unwrap()
        finish(5)
    }

    @Test
    fun testWithContextChildWaitWrappedContext() = runTest {
        expect(1)
        withContext(wrapperDispatcher(coroutineContext)) {
            expect(2)
            launch {
                // ^^^ schedules to main thread
                expect(4) // waits before return
            }
            expect(3)
            "OK".wrap()
        }.unwrap()
        finish(5)
    }

    @Test
    fun testIncompleteWithContextState() = runTest {
        lateinit var ctxJob: Job
        withContext(wrapperDispatcher(coroutineContext)) {
            ctxJob = coroutineContext[Job]!!
            ctxJob.invokeOnCompletion { }
        }

        ctxJob.join()
        assertTrue(ctxJob.isCompleted)
        assertFalse(ctxJob.isActive)
        assertFalse(ctxJob.isCancelled)
    }

    @Test
    fun testWithContextCancelledJob() = runTest {
        expect(1)
        val job = Job()
        job.cancel()
        try {
            withContext(job) {
                expectUnreached()
            }
        } catch (e: CancellationException) {
            expect(2)
        }
        finish(3)
    }

    @Test
    fun testWithContextCancelledThisJob() = runTest(
        expected = { it is CancellationException }
    ) {
        coroutineContext.cancel()
        withContext(wrapperDispatcher(coroutineContext)) {
            expectUnreached()
        }
        expectUnreached()
    }

    private class Wrapper(val value: String) : Incomplete {
        override val isActive: Boolean
            get() =  error("")
        override val list: NodeList?
            get() = error("")
    }

    private fun String.wrap() = Wrapper(this)
    private fun Wrapper.unwrap() = value
}
