/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.test.*

class PromiseTest {
    @Test
    fun testCompletionFromPromise() = runTest {
        var promiseEntered = false
        val p = promise {
            delay(1)
            promiseEntered = true
        }
        delay(2)
        p.await()
        assertTrue(promiseEntered)
    }
}