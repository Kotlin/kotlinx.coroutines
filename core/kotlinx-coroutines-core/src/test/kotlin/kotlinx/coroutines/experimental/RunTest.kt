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

package kotlinx.coroutines.experimental

import org.hamcrest.MatcherAssert.assertThat
import org.hamcrest.core.IsEqual
import org.junit.Test
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.CoroutineContext

class RunTest : TestBase() {
    @Test
    fun testSameContextNoSuspend() = runTest {
        expect(1)
        launch(coroutineContext) { // make sure there is not early dispatch here
            finish(5) // after main exits
        }
        expect(2)
        val result = run(coroutineContext) { // same context!
            expect(3) // still here
            "OK"
        }
        assertThat(result, IsEqual("OK"))
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
        val result = run(coroutineContext) { // same context!
            expect(3) // still here
            yield() // now yields to launch!
            expect(5)
            "OK"
        }
        assertThat(result, IsEqual("OK"))
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
        val result = run(coroutineContext + job) { // same context + new job
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
        assertThat(result, IsEqual("OK"))
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
        val result = run(coroutineContext + job) { // same context + new job
            expect(3) // still here
            yield() // now yields to launch!
            expect(5)
            job.cancel() // cancel out job!
            try {
                yield() // shall throw CancellationExpcetion
                expectUnreached()
            } catch (e: CancellationException) {
                expect(6)
            }
            "OK"
        }
        assertThat(result, IsEqual("OK"))
        finish(7)
    }

    @Test
    fun testCommonPoolNoSuspend() = runTest {
        expect(1)
        val result = run(CommonPool) {
            expect(2)
            "OK"
        }
        assertThat(result, IsEqual("OK"))
        finish(3)
    }

    @Test
    fun testCommonPoolWithSuspend() = runTest {
        expect(1)
        val result = run(CommonPool) {
            expect(2)
            delay(100)
            expect(3)
            "OK"
        }
        assertThat(result, IsEqual("OK"))
        finish(4)
    }

    @Test
    fun testRunCancellableDefault() = runTest(
        expected = { it is JobCancellationException }
    ) {
        val job = Job()
        job.cancel() // cancel before it has a chance to run
        run(job + wrapperDispatcher(coroutineContext)) {
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
        run(job + wrapperDispatcher(coroutineContext), CoroutineStart.ATOMIC) { // but start atomically
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
        run(job + wrapperDispatcher(coroutineContext), CoroutineStart.UNDISPATCHED) { // but start atomically
            finish(2)
            yield() // but will cancel here
            expectUnreached()
        }
    }

    private fun wrapperDispatcher(context: CoroutineContext): CoroutineContext {
        val dispatcher = context[ContinuationInterceptor] as CoroutineDispatcher
        return object : CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                dispatcher.dispatch(context, block)
            }
        }
    }
}