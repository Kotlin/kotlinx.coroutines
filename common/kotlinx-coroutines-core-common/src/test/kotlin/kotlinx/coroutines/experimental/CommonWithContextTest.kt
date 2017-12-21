
/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlin.test.*
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.CoroutineContext

class CommonWithContextTest : TestBase() {
    @Test
    fun testSameContextNoSuspend() = runTest {
        expect(1)
        launch(coroutineContext) { // make sure there is not early dispatch here
            finish(5) // after main exits
        }
        expect(2)
        val result = withContext(coroutineContext) { // same context!
            expect(3) // still here
            "OK"
        }
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
            "OK"
        }
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
        val result = withContext(coroutineContext + job) { // same context + new job
            expect(3) // still here
            job.cancel() // cancel out job!
            try {
                yield() // shall throw CancellationException
                expectUnreached()
            } catch (e: CancellationException) {
                expect(4)
            }
            "OK"
        }
        assertEquals("OK", result)
        expect(5)
        // will wait for the first coroutine
    }

    @Test
    fun testCancelWithJobWithSuspend() = runTest {
        expect(1)
        launch(coroutineContext) { // make sure there is not early dispatch to here
            expect(4)
        }
        expect(2)
        val job = Job()
        val result = withContext(coroutineContext + job) { // same context + new job
            expect(3) // still here
            yield() // now yields to launch!
            expect(5)
            job.cancel() // cancel out job!
            try {
                yield() // shall throw CancellationException
                expectUnreached()
            } catch (e: CancellationException) {
                expect(6)
            }
            "OK"
        }
        assertEquals("OK", result)
        finish(7)
    }

    @Test
    fun testRunCancellableDefault() = runTest(
        expected = { it is JobCancellationException }
    ) {
        val job = Job()
        job.cancel() // cancel before it has a chance to run
        withContext(job + wrapperDispatcher(coroutineContext)) {
            expectUnreached() // will get cancelled
        }
    }

    @Test
    fun testRunAtomicTryCancel() = runTest(
        expected = { it is JobCancellationException }
    ) {
        expect(1)
        val job = Job()
        job.cancel() // try to cancel before it has a chance to run
        withContext(job + wrapperDispatcher(coroutineContext), CoroutineStart.ATOMIC) { // but start atomically
            finish(2)
            yield() // but will cancel here
            expectUnreached()
        }
    }

    @Test
    fun testRunUndispatchedTryCancel() = runTest(
        expected = { it is JobCancellationException }
    ) {
        expect(1)
        val job = Job()
        job.cancel() // try to cancel before it has a chance to run
        withContext(job + wrapperDispatcher(coroutineContext), CoroutineStart.UNDISPATCHED) { // but start atomically
            finish(2)
            yield() // but will cancel here
            expectUnreached()
        }
    }

    @Test
    fun testRunWithException() = runTest {
        expect(1)
        var job: Job? = null
        job = launch(coroutineContext) {
            try {
                expect(3)
                withContext(wrapperDispatcher(coroutineContext)) {
                    expect(5)
                    job!!.cancel() // cancel itself
                    throw TestException() // but throw a different exception
                }
            } catch (e: Throwable) {
                expect(7)
                // make sure IOException, not CancellationException is thrown!
                assertTrue(e is TestException)
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

    private fun wrapperDispatcher(context: CoroutineContext): CoroutineContext {
        val dispatcher = context[ContinuationInterceptor] as CoroutineDispatcher
        return object : CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                dispatcher.dispatch(context, block)
            }
        }
    }

    private class TestException : Exception()
}