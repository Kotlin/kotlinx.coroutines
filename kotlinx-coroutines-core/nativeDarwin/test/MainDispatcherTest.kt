/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import platform.CoreFoundation.*
import platform.darwin.*
import kotlin.coroutines.*
import kotlin.test.*

class MainDispatcherTest : MainDispatcherTestBase() {

    private fun isMainThread(): Boolean = CFRunLoopGetCurrent() == CFRunLoopGetMain()

    override fun checkIsMainThread() = assertTrue(isMainThread())

    override fun checkNotMainThread() = assertFalse(isMainThread())

    // skip if already on the main thread, run blocking doesn't really work well with that
    override fun shouldSkipTesting(): Boolean = isMainThread()

    @Test
    fun testDispatchNecessityCheckWithMainImmediateDispatcher() = runTestOrSkip {
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
    fun testWithContext() = runTestOrSkip {
        expect(1)
        checkNotMainThread()
        withContext(Dispatchers.Main) {
            checkIsMainThread()
            expect(2)
        }
        checkNotMainThread()
        finish(3)
    }

    @Test
    fun testWithContextDelay() = runTestOrSkip {
        expect(1)
        withContext(Dispatchers.Main) {
            checkIsMainThread()
            expect(2)
            delay(100)
            checkIsMainThread()
            expect(3)
        }
        checkNotMainThread()
        finish(4)
    }

    @Test
    fun testWithTimeoutContextDelayNoTimeout() = runTestOrSkip {
        expect(1)
        withTimeout(1000) {
            withContext(Dispatchers.Main) {
                checkIsMainThread()
                expect(2)
                delay(100)
                checkIsMainThread()
                expect(3)
            }
        }
        checkNotMainThread()
        finish(4)
    }

    @Test
    fun testWithTimeoutContextDelayTimeout() = runTestOrSkip {
        expect(1)
        assertFailsWith<TimeoutCancellationException> {
            withTimeout(100) {
                withContext(Dispatchers.Main) {
                    checkIsMainThread()
                    expect(2)
                    delay(1000)
                    expectUnreached()
                }
            }
            expectUnreached()
        }
        checkNotMainThread()
        finish(3)
    }

    @Test
    fun testWithContextTimeoutDelayNoTimeout() = runTestOrSkip {
        expect(1)
        withContext(Dispatchers.Main) {
            withTimeout(1000) {
                checkIsMainThread()
                expect(2)
                delay(100)
                checkIsMainThread()
                expect(3)
            }
        }
        checkNotMainThread()
        finish(4)
    }

    @Test
    fun testWithContextTimeoutDelayTimeout() = runTestOrSkip {
        expect(1)
        assertFailsWith<TimeoutCancellationException> {
            withContext(Dispatchers.Main) {
                withTimeout(100) {
                    checkIsMainThread()
                    expect(2)
                    delay(1000)
                    expectUnreached()
                }
            }
            expectUnreached()
        }
        checkNotMainThread()
        finish(3)
    }
}
