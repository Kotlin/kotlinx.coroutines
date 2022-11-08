/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import platform.CoreFoundation.*
import platform.darwin.*
import kotlin.coroutines.*
import kotlin.test.*

class MainDispatcherTest : TestBase() {

    private fun isMainThread(): Boolean = CFRunLoopGetCurrent() == CFRunLoopGetMain()
    private fun canTestMainDispatcher() = !isMainThread()

    private fun runTestNotOnMainDispatcher(block: suspend CoroutineScope.() -> Unit) {
        // skip if already on the main thread, run blocking doesn't really work well with that
        if (!canTestMainDispatcher()) return
        runTest(block = block)
    }

    @Test
    fun testDispatchNecessityCheckWithMainImmediateDispatcher() = runTestNotOnMainDispatcher {
        val main = Dispatchers.Main.immediate
        assertTrue(main.isDispatchNeeded(EmptyCoroutineContext))
        withContext(Dispatchers.Default) {
            assertTrue(main.isDispatchNeeded(EmptyCoroutineContext))
            withContext(Dispatchers.Main) {
                assertFalse(main.isDispatchNeeded(EmptyCoroutineContext))
            }
            assertTrue(main.isDispatchNeeded(EmptyCoroutineContext))
        }
    }

    @Test
    fun testWithContext() = runTestNotOnMainDispatcher {
        expect(1)
        assertFalse(isMainThread())
        withContext(Dispatchers.Main) {
            assertTrue(isMainThread())
            expect(2)
        }
        assertFalse(isMainThread())
        finish(3)
    }

    @Test
    fun testWithContextDelay() = runTestNotOnMainDispatcher {
        expect(1)
        withContext(Dispatchers.Main) {
            assertTrue(isMainThread())
            expect(2)
            delay(100)
            assertTrue(isMainThread())
            expect(3)
        }
        assertFalse(isMainThread())
        finish(4)
    }

    @Test
    fun testWithTimeoutContextDelayNoTimeout() = runTestNotOnMainDispatcher {
        expect(1)
        withTimeout(1000) {
            withContext(Dispatchers.Main) {
                assertTrue(isMainThread())
                expect(2)
                delay(100)
                assertTrue(isMainThread())
                expect(3)
            }
        }
        assertFalse(isMainThread())
        finish(4)
    }

    @Test
    fun testWithTimeoutContextDelayTimeout() = runTestNotOnMainDispatcher {
        expect(1)
         assertFailsWith<TimeoutCancellationException> {
            withTimeout(100) {
                withContext(Dispatchers.Main) {
                    assertTrue(isMainThread())
                    expect(2)
                    delay(1000)
                    expectUnreached()
                }
            }
            expectUnreached()
        }
        assertFalse(isMainThread())
        finish(3)
    }

    @Test
    fun testWithContextTimeoutDelayNoTimeout() = runTestNotOnMainDispatcher {
        expect(1)
        withContext(Dispatchers.Main) {
            withTimeout(1000) {
                assertTrue(isMainThread())
                expect(2)
                delay(100)
                assertTrue(isMainThread())
                expect(3)
            }
        }
        assertFalse(isMainThread())
        finish(4)
    }

    @Test
    fun testWithContextTimeoutDelayTimeout() = runTestNotOnMainDispatcher {
        expect(1)
        assertFailsWith<TimeoutCancellationException> {
            withContext(Dispatchers.Main) {
                withTimeout(100) {
                    assertTrue(isMainThread())
                    expect(2)
                    delay(1000)
                    expectUnreached()
                }
            }
            expectUnreached()
        }
        assertFalse(isMainThread())
        finish(3)
    }
}
