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
import kotlin.coroutines.experimental.*
import kotlin.test.*

class SelectBiasTest : TestBase() {
    val n = 10_000

    @Test
    fun testBiased() = runTest {
        val d0 = async(coroutineContext) { 0 }
        val d1 = async(coroutineContext) { 1 }
        val counter = IntArray(2)
        repeat(n) {
            val selected = select<Int> {
                d0.onAwait { 0 }
                d1.onAwait { 1 }
            }
            counter[selected]++
        }
        assertEquals(n, counter[0])
        assertEquals(0, counter[1])
    }

    @Test
    fun testUnbiased() = runTest {
        val d0 = async(coroutineContext) { 0 }
        val d1 = async(coroutineContext) { 1 }
        val counter = IntArray(2)
        repeat(n) {
            val selected = selectUnbiased<Int> {
                d0.onAwait { 0 }
                d1.onAwait { 1 }
            }
            counter[selected]++
        }
        assertTrue(counter[0] >= n / 4)
        assertTrue(counter[1] >= n / 4)
    }
}