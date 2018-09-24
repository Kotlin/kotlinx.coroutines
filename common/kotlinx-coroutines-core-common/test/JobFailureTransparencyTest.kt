/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlin.test.*

class JobFailureTransparencyTest : TestBase() {
    @Test
    fun testFailAlone() = runTest(
        unhandled = listOf({ it -> it is TestException })
    ) {
        val job = launch(NonCancellable) {
            throw TestException()
        }
        job.join()
        checkFailed<TestException>(job)
    }

    @Test
    fun testFailChild() = runTest(
        unhandled = listOf({ it -> it is TestException })
    ) {
        val parent = Job()
        val job = launch(parent) {
            throw TestException()
        }
        job.join()
        checkFailed<TestException>(job)
        checkFailed<TestException>(parent)
    }

    private inline fun <reified E : Throwable> checkFailed(job: Job) {
        checkFailedState(job)
        var cause: Throwable? = null
        job.invokeOnCompletion { cause = it }
        assertTrue(cause is E, "cause = $cause")
    }

    private fun checkFailedState(job: Job) {
        assertFalse(job.isActive)
        assertTrue(job.isCompleted)
        assertTrue(job.isFailed)
        assertFalse(job.isCancelled)
    }

    private class TestException : Exception()
}