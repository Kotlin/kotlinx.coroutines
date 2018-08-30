/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*
import kotlin.test.*

class CoroutineExceptionHandlerTest : TestBase() {
    @Test
    fun testCoroutineExceptionHandlerCreator() = runTest {
        expect(1)
        var coroutineException: Throwable? = null
        val handler = CoroutineExceptionHandler { _, ex ->
            coroutineException = ex
            expect(3)
        }

        val job = launch(coroutineContext + handler, parent = Job()) {
            throw TestException()
        }

        expect(2)
        job.join()
        finish(4)
        assertTrue(coroutineException is TestException)
    }

    private class TestException: RuntimeException()
}
