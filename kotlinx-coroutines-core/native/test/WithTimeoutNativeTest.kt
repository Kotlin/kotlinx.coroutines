/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*
import kotlin.time.*
import kotlin.native.concurrent.freeze

class WithTimeoutNativeTest {
    @OptIn(ExperimentalTime::class)
    @Test
    fun `withTimeout should not raise an exception when parent job is frozen`() = runBlocking {
        this.coroutineContext[Job.Key]!!.freeze()
        try {
            withTimeout(Duration.seconds(Int.MAX_VALUE)) {}
        } catch (error: Throwable) {
            fail("withTimeout has raised an exception.", error)
        }
    }
}
