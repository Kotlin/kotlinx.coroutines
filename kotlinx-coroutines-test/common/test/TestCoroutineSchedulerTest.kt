/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.test.*

class TestCoroutineSchedulerTest {
    @Test
    /** Tests that `TestCoroutineScheduler` attempts to detect if there are several instances of it. */
    fun testContextElement() {
        runBlockingTest {
            assertFailsWith<IllegalStateException> {
                withContext(TestCoroutineDispatcher()) {
                }
            }
        }
    }
}
