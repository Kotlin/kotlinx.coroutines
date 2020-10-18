/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

class CancellableContinuationTest : TestBase() {
    @Test
    fun testResumeWithExceptionAndResumeWithException() = runTest {
        var continuation: Continuation<Unit>? = null
        val job = launch {
            try {
                expect(2)
                suspendCancellableCoroutine<Unit> { c ->
                    continuation = c
                }
            } catch (e: TestException) {
                expect(3)
            }
        }
        expect(1)
        yield()
        continuation!!.resumeWithException(TestException())
        yield()
        assertFailsWith<IllegalStateException> { continuation!!.resumeWithException(TestException()) }
        job.join()
        finish(4)
    }

    @Test
    fun testResumeAndResumeWithException() = runTest {
        var continuation: Continuation<Unit>? = null
        val job = launch {
            expect(2)
            suspendCancellableCoroutine<Unit> { c ->
                continuation = c
            }
            expect(3)
        }
        expect(1)
        yield()
        continuation!!.resume(Unit)
        job.join()
        assertFailsWith<IllegalStateException> { continuation!!.resumeWithException(TestException()) }
        finish(4)
    }

    @Test
    fun testResumeAndResume() = runTest {
        var continuation: Continuation<Unit>? = null
        val job = launch {
            expect(2)
            suspendCancellableCoroutine<Unit> { c ->
                continuation = c
            }
            expect(3)
        }
        expect(1)
        yield()
        continuation!!.resume(Unit)
        job.join()
        assertFailsWith<IllegalStateException> { continuation!!.resume(Unit) }
        finish(4)
    }

    /**
     * Cancelling outer job may, in practise, race with attempt to resume continuation and resumes
     * should be ignored. Here suspended coroutine is cancelled but then resumed with exception.
     */
    @Test
    fun testCancelAndResumeWithException() = runTest {
        var continuation: Continuation<Unit>? = null
        val job = launch {
            try {
                expect(2)
                suspendCancellableCoroutine<Unit> { c ->
                    continuation = c
                }
            } catch (e: CancellationException) {
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
                suspendCancellableCoroutine<Unit> { c ->
                    continuation = c
                }
            } catch (e: CancellationException) {
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
}