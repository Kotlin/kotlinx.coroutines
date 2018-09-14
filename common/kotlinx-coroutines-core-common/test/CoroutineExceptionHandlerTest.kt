/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.test.*

class CoroutineExceptionHandlerTest : TestBase() {
    // Parent Job() does not handle exception --> handler is invoked on child crash
    @Test
    fun testJob() = runTest {
        expect(1)
        var coroutineException: Throwable? = null
        val handler = CoroutineExceptionHandler { _, ex ->
            coroutineException = ex
            expect(3)
        }
        val parent = Job()
        val job = launch(handler + parent) {
            throw TestException()
        }
        expect(2)
        job.join()
        finish(4)
        assertTrue(coroutineException is TestException)
        assertTrue(parent.isFailed)
    }

    // Parent CompletableDeferred() "handles" exception --> handler is NOT invoked on child crash
    @Test
    fun testCompletableDeferred() = runTest {
        expect(1)
        val handler = CoroutineExceptionHandler { _, ex ->
            expectUnreached()
        }
        val parent = CompletableDeferred<Unit>()
        val job = launch(handler + parent) {
            throw TestException()
        }
        expect(2)
        job.join()
        finish(3)
        assertTrue(parent.isFailed)
        assertTrue(parent.getCompletionExceptionOrNull() is TestException)
    }

    private class TestException: RuntimeException()
}
