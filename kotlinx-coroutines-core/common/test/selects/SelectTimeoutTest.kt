/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlin.test.*

class SelectTimeoutTest : TestBase() {
    @Test
    fun testBasic() = runTest {
        expect(1)
        val result = select<String> {
            onTimeout(1000) {
                expectUnreached()
                "FAIL"
            }
            onTimeout(100) {
                expect(2)
                "OK"
            }
            onTimeout(500) {
                expectUnreached()
                "FAIL"
            }
        }
        assertEquals("OK", result)
        finish(3)
    }

    @Test
    fun testZeroTimeout() = runTest {
        expect(1)
        val result = select<String> {
            onTimeout(1000) {
                expectUnreached()
                "FAIL"
            }
            onTimeout(0) {
                expect(2)
                "OK"
            }
        }
        assertEquals("OK", result)
        finish(3)
    }

    @Test
    fun testNegativeTimeout() = runTest {
        expect(1)
        val result = select<String> {
            onTimeout(1000) {
                expectUnreached()
                "FAIL"
            }
            onTimeout(-10) {
                expect(2)
                "OK"
            }
        }
        assertEquals("OK", result)
        finish(3)
    }
}
