/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class EnsureActiveTest : TestBase() {

    private val job = Job()
    private val scope = CoroutineScope(job + CoroutineExceptionHandler { _, _ ->  })

    @Test
    fun testIsActive() = runTest {
        expect(1)
        scope.launch(Dispatchers.Unconfined) {
            ensureActive()
            coroutineContext.ensureActive()
            coroutineContext[Job]!!.ensureActive()
            expect(2)
            delay(Long.MAX_VALUE)
        }

        expect(3)
        job.ensureActive()
        scope.ensureActive()
        scope.coroutineContext.ensureActive()
        job.cancelAndJoin()
        finish(4)
    }

    @Test
    fun testIsCompleted() = runTest {
        expect(1)
        scope.launch(Dispatchers.Unconfined) {
            ensureActive()
            coroutineContext.ensureActive()
            coroutineContext[Job]!!.ensureActive()
            expect(2)
        }

        expect(3)
        job.complete()
        job.join()
        assertFailsWith<JobCancellationException> { job.ensureActive() }
        assertFailsWith<JobCancellationException> { scope.ensureActive() }
        assertFailsWith<JobCancellationException> { scope.coroutineContext.ensureActive() }
        finish(4)
    }


    @Test
    fun testIsCancelled() = runTest {
        expect(1)
        scope.launch(Dispatchers.Unconfined) {
            ensureActive()
            coroutineContext.ensureActive()
            coroutineContext[Job]!!.ensureActive()
            expect(2)
            throw TestException()
        }

        expect(3)
        checkException { job.ensureActive() }
        checkException { scope.ensureActive() }
        checkException { scope.coroutineContext.ensureActive() }
        finish(4)
    }

    @Test
    fun testEnsureActiveWithEmptyContext() = runTest {
        withEmptyContext {
            ensureActive() // should not do anything
        }
    }

    private inline fun checkException(block: () -> Unit) {
        val result = runCatching(block)
        val exception = result.exceptionOrNull() ?: fail()
        assertTrue(exception is JobCancellationException)
        assertTrue(exception.cause is TestException)
    }
}
