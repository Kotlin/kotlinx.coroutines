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

package kotlinx.coroutines.experimental.sync

import kotlinx.coroutines.experimental.*
import kotlin.test.*

class MutexStressTest : TestBase() {
    @Test
    fun testStress() = runTest {
        val n = 1000 * stressTestMultiplier
        val k = 100
        var shared = 0
        val mutex = Mutex()
        val jobs = List(n) {
            launch {
                repeat(k) {
                    mutex.lock()
                    shared++
                    mutex.unlock()
                }
            }
        }
        jobs.forEach { it.join() }
        println("Shared value = $shared")
        assertEquals(n * k, shared)
    }
}