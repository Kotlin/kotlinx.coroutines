/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

class CancellableContinuationJvmTest : TestBase() {
    @Test
    fun testToString() = runTest {
        checkToString()
    }

    private suspend fun checkToString() {
        suspendCancellableCoroutine<Unit> {
            it.resume(Unit)
            assertTrue(it.toString().contains("kotlinx/coroutines/CancellableContinuationJvmTest.checkToString(CancellableContinuationJvmTest.kt:16"))
        }
    }
}
