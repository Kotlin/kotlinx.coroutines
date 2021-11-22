/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.test.*

/** These are tests that we want to fail. They are here so that, when the issue is fixed, their failure indicates that
 * everything is better now. */
class FailingTests {
    @Test
    fun testRunTestLoopShutdownOnTimeout() = testResultMap({ fn ->
        assertFailsWith<IllegalStateException> { fn() }
    }) {
        runTest(dispatchTimeoutMs = 1) {
            withContext(Dispatchers.Default) {
                delay(10000)
            }
            fail("shouldn't be reached")
        }
    }

}