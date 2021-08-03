/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*
import platform.CoreFoundation.*
import platform.darwin.*

class MainDispatcherTest : TestBase() {

    private fun isMainThread(): Boolean = CFRunLoopGetCurrent() == CFRunLoopGetMain()

    @Test
    fun testDispatchNecessityCheckWithMainImmediateDispatcher() {
        if (isMainThread()) return
        runTest {
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
    }

    @Test
    fun testWithContext() {
        if (isMainThread()) return // skip if already on the main thread, run blocking doesn't really works well with that
        runTest {
            expect(1)
            assertFalse(isMainThread())
            withContext(Dispatchers.Main) {
                assertTrue(isMainThread())
                expect(2)
            }
            assertFalse(isMainThread())
            finish(3)
        }
    }

    @Test
    fun testWithContextDelay() {
        if (isMainThread()) return // skip if already on the main thread, run blocking doesn't really works well with that
        runTest {
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
    }

    @Test
    fun testWithTimeoutContextDelayNoTimeout() {
        if (isMainThread()) return // skip if already on the main thread, run blocking doesn't really works well with that
        runTest {
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
    }

    @Test
    fun testWithTimeoutContextDelayTimeout() {
        if (isMainThread()) return // skip if already on the main thread, run blocking doesn't really works well with that
        runTest {
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
    }

    @Test
    fun testWithContextTimeoutDelayNoTimeout() {
        if (isMainThread()) return // skip if already on the main thread, run blocking doesn't really works well with that
        runTest {
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
    }

    @Test
    fun testWithContextTimeoutDelayTimeout() {
        if (isMainThread()) return // skip if already on the main thread, run blocking doesn't really works well with that
        runTest {
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
}
