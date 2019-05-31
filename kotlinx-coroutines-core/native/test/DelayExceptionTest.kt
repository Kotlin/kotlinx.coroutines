/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

class DelayExceptionTest : TestBase() {
    private object Dispatcher : CoroutineDispatcher() {
        override fun isDispatchNeeded(context: CoroutineContext): Boolean = true
        override fun dispatch(context: CoroutineContext, block: Runnable) { block.run() }
    }

    private lateinit var exception: Throwable


    @Test
    fun testThrowsTce() {
        CoroutineScope(Dispatcher + CoroutineExceptionHandler { _, e -> exception = e }).launch {
            delay(10)
        }

        assertTrue(exception is IllegalStateException)
    }

    @Test
    fun testMaxDelay() = runBlocking {
        expect(1)
        val job = launch {
            expect(2)
            delay(Long.MAX_VALUE)
        }
        yield()
        job.cancel()
        finish(3)
    }
}
