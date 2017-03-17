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

package kotlinx.coroutines.experimental.reactive

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import org.hamcrest.core.IsEqual
import org.junit.Assert.assertThat
import org.junit.Assert.assertTrue
import org.junit.Test

/**
 * Test emitting multiple values with [publish].
 */
class PublisherMultiTest : TestBase() {
    @Test
    fun testConcurrentStress() = runBlocking<Unit> {
        val n = 10_000 * stressTestMultiplier
        val observable = publish<Int>(CommonPool) {
            // concurrent emitters (many coroutines)
            val jobs = List(n) {
                // launch
                launch(CommonPool) {
                    send(it)
                }
            }
            jobs.forEach { it.join() }
        }
        val resultSet = mutableSetOf<Int>()
        observable.consumeEach {
            assertTrue(resultSet.add(it))
        }
        assertThat(resultSet.size, IsEqual(n))
    }
}
