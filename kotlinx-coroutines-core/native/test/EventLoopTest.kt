/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

/**
 * Ensure that there are no leaks because of various delay usage.
 */
class EventLoopTest : TestBase() {
    @Test
    fun testDelayWait() = runTest {
        expect(1)
        delay(1)
        finish(2)
    }

    @Test
    fun testDelayCancel() = runTest {
        expect(1)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            delay(100)
            expectUnreached()
        }
        expect(3)
        job.cancel()
        finish(4)
    }

    @Test
    fun testCancellableContinuationResumeUndispatchedCancelled() = runTest {
        expect(1)
        var cont: CancellableContinuation<Unit>? = null
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            assertFailsWith<CancellationException> {
                suspendCancellableCoroutine<Unit> { cont = it }
            }
            expect(5)
        }
        expect(3)
        with(cont!!) {
            cancel()
            // already cancelled, so nothing should happen on resumeUndispatched
            (coroutineContext[ContinuationInterceptor] as CoroutineDispatcher).resumeUndispatched(Unit)
        }
        expect(4)
        yield()
        finish(6)
    }
}