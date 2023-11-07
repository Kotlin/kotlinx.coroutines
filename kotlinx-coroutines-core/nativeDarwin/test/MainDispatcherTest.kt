/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import platform.CoreFoundation.*
import platform.darwin.*
import kotlin.coroutines.*
import kotlin.test.*

class MainDispatcherTest : MainDispatcherTestBase() {

    override fun isMainThread(): Boolean = CFRunLoopGetCurrent() == CFRunLoopGetMain()

    // skip if already on the main thread, run blocking doesn't really work well with that
    override fun shouldSkipTesting(): Boolean = isMainThread()

    @Test
    fun testDispatchNecessityCheckWithMainImmediateDispatcher() = runTestOrSkip {
        val immediate = Dispatchers.Main.immediate
        assertTrue(immediate.isDispatchNeeded(EmptyCoroutineContext))
        withContext(Dispatchers.Default) {
            assertTrue(immediate.isDispatchNeeded(EmptyCoroutineContext))
            withContext(Dispatchers.Main) {
                assertFalse(immediate.isDispatchNeeded(EmptyCoroutineContext))
            }
            assertTrue(immediate.isDispatchNeeded(EmptyCoroutineContext))
        }
    }
}
