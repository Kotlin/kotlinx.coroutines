/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlin.test.*
import kotlin.time.*

@ExperimentalTime
class SelectTimeoutDurationTest : TestBase() {
    @Test
    fun testBasic() = runTest {
        expect(1)
        val result = select<String> {
            onTimeout(Duration.milliseconds(1000)) {
                expectUnreached()
                "FAIL"
            }
            onTimeout(Duration.milliseconds(100)) {
                expect(2)
                "OK"
            }
            onTimeout(Duration.milliseconds(500)) {
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
            onTimeout(Duration.seconds(1)) {
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
            onTimeout(Duration.seconds(1)) {
                expectUnreached()
                "FAIL"
            }
            onTimeout(-Duration.milliseconds(10)) {
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
                onTimeout(-Duration.seconds(1)) {
                    0
                }
                onTimeout(Duration.ZERO) {
                    1
                }
                onTimeout(Duration.seconds(1)) {
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
