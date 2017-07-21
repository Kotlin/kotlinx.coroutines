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

import kotlinx.coroutines.experimental.runBlocking
import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import org.junit.Test

class ChannelsTest {
    @Test
    fun testEmptyList() = runBlocking {
        val channel = Channel<String>()
        channel.close()

        assertTrue(channel.collectList().isEmpty())
    }

    @Test
    fun testCollectList() = runBlocking {
        val values = listOf("A", "B", "F")
        val channel = Channel<String>(values.size)
        values.forEach {
            channel.send(it)
        }
        channel.close()

        assertEquals(channel.collectList(), values)
    }

    @Test
    fun testEmptySet() = runBlocking {
        val channel = Channel<String>()
        channel.close()

        assertTrue(channel.collectSet().isEmpty())
    }

    @Test
    fun testCollectSet() = runBlocking {
        val values = setOf("A", "B", "F")
        val channel = Channel<String>(values.size)
        values.forEach {
            channel.send(it)
        }
        channel.close()

        assertEquals(channel.collectSet(), values)
    }

    @Test
    fun testEmptySequence() = runBlocking {
        val channel = Channel<String>()
        channel.close()

        assertTrue(channel.collectSequence().count() == 0)
    }

    @Test
    fun testCollectSequence() = runBlocking {
        val values = listOf("A", "B", "F")
        val channel = Channel<String>(values.size)
        values.forEach {
            channel.send(it)
        }
        channel.close()

        assertEquals(channel.collectSequence().toList(), values.toList())
    }

    @Test
    fun testEmptyMap() = runBlocking {
        val channel = Channel<String>()
        channel.close()

        assertTrue(channel.collectMap { it }.isEmpty())
    }

    @Test
    fun testCollectMap() = runBlocking {
        val values = mapOf("A" to 1, "B" to 2, "F" to 3)
        val channel = Channel<Pair<String, Int>>(values.size)
        values.entries.forEach {
            channel.send(it.key to it.value)
        }
        channel.close()

        val expected = values.mapValues { (k, v) -> k to v }

        assertEquals(expected, channel.collectMap { it.first })
    }

}