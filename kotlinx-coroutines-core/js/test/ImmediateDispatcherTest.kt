/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

class ImmediateDispatcherTest : MainDispatcherTestBase() {

    /** Tests that entering [MainCoroutineDispatcher.immediate] takes priority even outside [Dispatchers.Main]. */
    @Test
    fun testImmediate() = runTest {
        expect(1)
        val job = launch { expect(3) }
        assertTrue(Dispatchers.Main.immediate.isDispatchNeeded(currentCoroutineContext()))
        withContext(Dispatchers.Main.immediate) {
            expect(2)
        }
        job.join()
        finish(4)
    }

    @Test
    fun testMain() = runTest {
        expect(1)
        val job = launch { expect(2) }
        withContext(Dispatchers.Main) {
            expect(3)
        }
        job.join()
        finish(4)
    }

    override fun isMainThread(): Boolean? = null

    override fun scheduleOnMainQueue(block: () -> Unit) {
        Dispatchers.Default.dispatch(EmptyCoroutineContext, Runnable { block() })
    }
}
