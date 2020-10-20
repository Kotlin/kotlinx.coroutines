/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

/**
 * When using [suspendCoroutine] from the standard library the continuation must be dispatched atomically,
 * without checking for cancellation at any point in time.
 */
class DispatchedContinuationTest : TestBase() {
    private lateinit var cont: Continuation<String>

    @Test
    fun testCancelThenResume() = runTest {
        expect(1)
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            coroutineContext[Job]!!.cancel()
            // a regular suspendCoroutine will still suspend despite the fact that coroutine was cancelled
            val value = suspendCoroutine<String> {
                expect(3)
                cont = it
            }
            expect(6)
            assertEquals("OK", value)
        }
        expect(4)
        cont.resume("OK")
        expect(5)
        yield() // to the launched job
        finish(7)
    }

    @Test
    fun testCancelThenResumeUnconfined() = runTest {
        expect(1)
        launch(Dispatchers.Unconfined) {
            expect(2)
            coroutineContext[Job]!!.cancel()
            // a regular suspendCoroutine will still suspend despite the fact that coroutine was cancelled
            val value = suspendCoroutine<String> {
                expect(3)
                cont = it
            }
            expect(5)
            assertEquals("OK", value)
        }
        expect(4)
        cont.resume("OK") // immediately resumes -- because unconfined
        finish(6)
    }

    @Test
    fun testResumeThenCancel() = runTest {
        expect(1)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val value = suspendCoroutine<String> {
                expect(3)
                cont = it
            }
            expect(7)
            assertEquals("OK", value)
        }
        expect(4)
        cont.resume("OK")
        expect(5)
        // now cancel the job, which the coroutine is waiting to be dispatched
        job.cancel()
        expect(6)
        yield() // to the launched job
        finish(8)
    }
}