/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

class DelayExceptionTest : TestBase() {

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
