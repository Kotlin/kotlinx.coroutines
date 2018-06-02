/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.selects

import kotlinx.coroutines.experimental.*
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

    @Test
    fun testUnbiasedNegativeTimeout() = runTest {
        val counters = intArrayOf(0, 0, 0)
        val iterations =10_000
        for (i in 0..iterations) {
            val result = selectUnbiased<Int> {
                onTimeout(-10) {
                    0
                }
                onTimeout(0) {
                    1
                }
                onTimeout(10) {
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
