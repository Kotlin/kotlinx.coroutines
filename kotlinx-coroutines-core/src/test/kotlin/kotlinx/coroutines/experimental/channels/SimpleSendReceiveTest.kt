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

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import org.hamcrest.core.IsEqual
import org.junit.Assert.assertThat
import org.junit.Assert.assertTrue
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized

@RunWith(Parameterized::class)
class SimpleSendReceiveTest(
    val kind: TestChannelKind,
    val n: Int
) {
    companion object {
        @Parameterized.Parameters(name = "{0}, n={1}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = TestChannelKind.values().flatMap { kind ->
            listOf(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 100, 1000).map { n ->
                arrayOf<Any>(kind, n)
            }
        }
    }

    val channel = kind.create()

    @Test
    fun testSimpleSendReceive() = runBlocking {
        launch(CommonPool) {
            repeat(n) { channel.send(it) }
            channel.close()
        }
        var expected = 0
        for (x in channel) {
            if (kind != TestChannelKind.CONFLATED) {
                assertThat(x, IsEqual(expected++))
            } else {
                assertTrue(x >= expected)
                expected = x + 1
            }
        }
        if (kind != TestChannelKind.CONFLATED) {
            assertThat(expected, IsEqual(n))
        }
    }
}