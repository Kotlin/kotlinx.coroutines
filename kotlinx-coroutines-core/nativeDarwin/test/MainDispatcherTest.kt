/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class MainDispatcherTest : TestBase() {
    private val testThread = currentThread()

    @Test
    fun testWithContext() {
        if (testThread == mainThread) return // skip if already on the main thread
        runTest {
            expect(1)
            withContext(Dispatchers.Main) {
                assertEquals(mainThread, currentThread())
                expect(2)
            }
            assertEquals(testThread, currentThread())
            finish(3)
        }
    }

    @Test
    fun testWithContextDelay() {
        if (testThread == mainThread) return // skip if already on the main thread
        runTest {
            expect(1)
            withContext(Dispatchers.Main) {
                assertEquals(mainThread, currentThread())
                expect(2)
                delay(100)
                assertEquals(mainThread, currentThread())
                expect(3)
            }
            assertEquals(testThread, currentThread())
            finish(4)
        }
    }

    @Test
    fun testWithTimeoutContextDelayNoTimeout() {
        if (testThread == mainThread) return // skip if already on the main thread
        runTest {
            expect(1)
            withTimeout(1000) {
                withContext(Dispatchers.Main) {
                    assertEquals(mainThread, currentThread())
                    expect(2)
                    delay(100)
                    assertEquals(mainThread, currentThread())
                    expect(3)
                }
            }
            assertEquals(testThread, currentThread())
            finish(4)
        }
    }

    @Test
    fun testWithTimeoutContextDelayTimeout() {
        if (testThread == mainThread) return // skip if already on the main thread
        runTest {
            expect(1)
             assertFailsWith<TimeoutCancellationException> {
                withTimeout(100) {
                    withContext(Dispatchers.Main) {
                        assertEquals(mainThread, currentThread())
                        expect(2)
                        delay(1000)
                        expectUnreached()
                    }
                }
                expectUnreached()
            }
            assertEquals(testThread, currentThread())
            finish(3)
        }
    }

    @Test
    fun testWithContextTimeoutDelayNoTimeout() {
        if (testThread == mainThread) return // skip if already on the main thread
        runTest {
            expect(1)
            withContext(Dispatchers.Main) {
                withTimeout(1000) {
                    assertEquals(mainThread, currentThread())
                    expect(2)
                    delay(100)
                    assertEquals(mainThread, currentThread())
                    expect(3)
                }
            }
            assertEquals(testThread, currentThread())
            finish(4)
        }
    }

    @Test
    fun testWithContextTimeoutDelayTimeout() {
        if (testThread == mainThread) return // skip if already on the main thread
        runTest {
            expect(1)
            assertFailsWith<TimeoutCancellationException> {
                withContext(Dispatchers.Main) {
                    withTimeout(100) {
                        assertEquals(mainThread, currentThread())
                        expect(2)
                        delay(1000)
                        expectUnreached()
                    }
                }
                expectUnreached()
            }
            assertEquals(testThread, currentThread())
            finish(3)
        }
    }
}
