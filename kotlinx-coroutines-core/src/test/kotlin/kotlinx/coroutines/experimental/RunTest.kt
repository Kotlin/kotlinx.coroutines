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
    fun testSameContextNoSuspend() = runBlocking<Unit> {
        expect(1)
        launch(coroutineContext) { // make sure there is not early dispatch here
            expectUnreached() // will terminate before it has a chance to start
        }
        expect(2)
        val result = run(coroutineContext) { // same context!
            expect(3) // still here
            "OK"
        }
        assertThat(result, IsEqual("OK"))
        finish(4)
    }

    @Test
    fun testSameContextWithSuspend() = runBlocking<Unit> {
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
    fun testCancelWithJobNoSuspend() = runBlocking<Unit> {
        expect(1)
        launch(coroutineContext) { // make sure there is not early dispatch to here
            expectUnreached() // will terminate before it has a chance to start
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
        finish(5)
    }

    @Test
    fun testCancelWithJobWithSuspend() = runBlocking<Unit> {
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
    fun testCommonPoolNoSuspend() = runBlocking<Unit> {
        expect(1)
        val result = run(CommonPool) {
            expect(2)
            "OK"
        }
        assertThat(result, IsEqual("OK"))
        finish(3)
    }

    @Test
    fun testCommonPoolWithSuspend() = runBlocking<Unit> {
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

    @Test(expected = CancellationException::class)
    fun testRunCancellableDefault() = runBlocking<Unit> {
        val job = Job()
        job.cancel() // cancel before it has a chance to run
        run(job + wrapperDispatcher(coroutineContext)) {
            expectUnreached() // will get cancelled
        }
    }

    @Test(expected = CancellationException::class)
    fun testRunAtomicTryCancel() = runBlocking<Unit> {
        expect(1)
        val job = Job()
        job.cancel() // try to cancel before it has a chance to run
        run(job + wrapperDispatcher(coroutineContext), CoroutineStart.ATOMIC) { // but start atomically
            finish(2)
            yield() // but will cancel here
            expectUnreached()
        }
    }

    @Test(expected = CancellationException::class)
    fun testRunUndispatchedTryCancel() = runBlocking<Unit> {
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