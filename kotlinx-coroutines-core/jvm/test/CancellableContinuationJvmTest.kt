/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

class CancellableContinuationJvmTest : TestBase() {
    @Test
    fun testToString() = runTest {
        checkToString()
    }

    private suspend fun checkToString() {
        suspendCancellableCoroutine<Unit> {
            it.resume(Unit)
            assertTrue(it.toString().contains("kotlinx.coroutines.CancellableContinuationJvmTest.checkToString(CancellableContinuationJvmTest.kt"))
        }
        suspend {}() // Eliminate tail-call optimization
    }

    @Test
    fun testExceptionIsNotReported() = runTest({ it is CancellationException }) {
        val ctx = coroutineContext
        suspendCancellableCoroutine<Unit> {
            ctx.cancel()
            it.resumeWith(Result.failure(TestException()))
        }
    }

    @Test
    fun testBlockingIntegration() = runTest {
        val source = BlockingSource()
        val job = launch(Dispatchers.Default) {
            source.await()
        }
        source.cancelAndJoin(job)
    }

    @Test
    fun testBlockingIntegrationAlreadyCancelled() = runTest {
        val source = BlockingSource()
        val job = launch(Dispatchers.Default) {
            cancel()
            source.await()
        }
        source.cancelAndJoin(job)
    }

    private suspend fun BlockingSource.cancelAndJoin(job: Job) {
        while (!hasSubscriber) {
            Thread.sleep(10)
        }
        job.cancelAndJoin()
    }

    private suspend fun BlockingSource.await() = suspendCancellableCoroutine<Unit> {
        it.invokeOnCancellation { this.cancel() }
        subscribe()
    }

    private class BlockingSource {
        @Volatile
        private var isCancelled = false

        @Volatile
        public var hasSubscriber = false

        public fun subscribe() {
            hasSubscriber = true
            while (!isCancelled) {
                Thread.sleep(10)
            }
        }

        public fun cancel() {
            isCancelled = true
        }
    }
}
