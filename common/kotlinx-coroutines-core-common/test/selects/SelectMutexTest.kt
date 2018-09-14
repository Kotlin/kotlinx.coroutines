/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.selects

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.sync.*
import kotlin.test.*

class SelectMutexTest : TestBase() {
    @Test
    fun testSelectLock() = runTest {
        val mutex = Mutex()
        expect(1)
        launch { // ensure that it is not scheduled earlier than needed
            finish(4) // after main exits
        }
        val res = select<String> {
            mutex.onLock {
                assertTrue(mutex.isLocked)
                expect(2)
                "OK"
            }
        }
        assertEquals("OK", res)
        expect(3)
        // will wait for the first coroutine
    }

    @Test
    fun testSelectLockWait() = runTest {
        val mutex = Mutex(true) // locked
        expect(1)
        launch {
            expect(3)
            val res = select<String> {
                // will suspended
                mutex.onLock {
                    assertTrue(mutex.isLocked)
                    expect(6)
                    "OK"
                }
            }
            assertEquals("OK", res)
            expect(7)
        }
        expect(2)
        yield() // to launched coroutine
        expect(4)
        mutex.unlock()
        expect(5)
        yield() // to resumed select
        finish(8)
    }
}