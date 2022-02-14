/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlin.test.*
import kotlin.time.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.seconds

class SelectTimeoutDurationTest : TestBase() {
    @Test
    fun testBasic() = runTest {
        expect(1)
        val result = select<String> {
            onTimeout(1000.milliseconds) {
                expectUnreached()
                "FAIL"
            }
            onTimeout(100.milliseconds) {
                expect(2)
                "OK"
            }
            onTimeout(500.milliseconds) {
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
            onTimeout(1.seconds) {
                expectUnreached()
                "FAIL"
            }
            onTimeout(Duration.ZERO) {
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
            onTimeout(1.seconds) {
                expectUnreached()
                "FAIL"
            }
            onTimeout(-10.milliseconds) {
                expect(2)
                "OK"
            }
        }
        assertEquals("OK", result)
        finish(3)
    }

    @Test
    fun testUnbiasedNegativeTimeout() = runTest {
        val counters = intArrayOf(0, 0, 0)
        val iterations =10_000
        for (i in 0..iterations) {
            val result = selectUnbiased<Int> {
                onTimeout((-1).seconds) {
                    0
                }
                onTimeout(Duration.ZERO) {
                    1
                }
                onTimeout(1.seconds) {
                    expectUnreached()
                    2
                }
            }
            ++counters[result]
        }
        assertEquals(0, counters[2])
        assertTrue { counters[0] >  iterations / 4 }
        assertTrue { counters[1] >  iterations / 4 }
    }
}
