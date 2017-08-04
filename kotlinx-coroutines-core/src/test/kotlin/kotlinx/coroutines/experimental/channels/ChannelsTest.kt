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
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Assert.*
import org.junit.Test

class ChannelsTest {

    private val testList = listOf(1, 2, 3)

    @Test
    fun testAsReceiveChannel() = runBlocking {
        assertEquals(testList, testList.asReceiveChannel().toList())
    }

    @Test
    fun testAsSequence() {
        assertEquals(testList, testList.asReceiveChannel().asSequence().toList())
    }

    @Test
    fun testAssociateBy() = runBlocking {
        assertEquals(testList.associateBy { it % 2 }, testList.asReceiveChannel().associateBy { it % 2 })
    }

    @Test
    fun testAsSequenceLazy() = runBlocking {
        val numbers = produce(CommonPool) {
            repeat(2) { i ->
                send(i)
            }
            fail()
        }
        val take2 = numbers
                .asSequence()
                .take(2)
                .toList()

        assertEquals(listOf(0, 1), take2)
    }

    @Test
    fun testDistinctBy() = runBlocking {
        assertEquals(testList.distinctBy { it % 2 }.toList(), testList.asReceiveChannel().distinctBy { it % 2 }.toList())

    }

    @Test
    fun testDrainTo() = runBlocking {
        val target = mutableListOf<Int>()
        testList.asReceiveChannel().drainTo(target)

        assertEquals(testList, target)
    }

    @Test
    fun testDrop() = runBlocking {
        for (i in 0..testList.size) {
            assertEquals("Drop $i", testList.drop(i), testList.asReceiveChannel().drop(i).toList())
        }
    }

    @Test
    fun testElementAtOrElse() = runBlocking {
        assertEquals(testList.elementAtOrElse(2) { 42 }, testList.asReceiveChannel().elementAtOrElse(2) { 42 })
        assertEquals(testList.elementAtOrElse(9) { 42 }, testList.asReceiveChannel().elementAtOrElse(9) { 42 })
    }

    @Test
    fun testFirst() = runBlocking {
        for (i in testList) {
            assertEquals(testList.first { it == i }, testList.asReceiveChannel().first { it == i })
        }
        try {
            testList.asReceiveChannel().first { it == 9 }
            fail()
        } catch (nse: NoSuchElementException) {
        }
    }

    @Test
    fun testFirstOrNull() = runBlocking {
        assertEquals(testList.firstOrNull { it == 2 }, testList.asReceiveChannel().firstOrNull { it == 2 })
        assertEquals(testList.firstOrNull { it == 9 }, testList.asReceiveChannel().firstOrNull { it == 9 })
    }

    @Test
    fun testFlatMap() = runBlocking {
        assertEquals(testList.flatMap { (0..it).toList() }, testList.asReceiveChannel().flatMap { (0..it).asReceiveChannel() }.toList())

    }

    @Test
    fun testFold() = runBlocking {
        assertEquals(testList.fold(mutableListOf(42)) { acc, e -> acc.apply { add(e) } },
                testList.asReceiveChannel().fold(mutableListOf(42)) { acc, e -> acc.apply { add(e) } }.toList())

    }

    @Test
    fun testGroupBy() = runBlocking {
        assertEquals(testList.groupBy({ -it }, { it + 100 }), testList.asReceiveChannel().groupBy({ -it }, { it + 100 }).toMap())

    }

    @Test
    fun testMap() = runBlocking {
        assertEquals(testList.map { it + 10 }, testList.asReceiveChannel().map { it + 10 }.toList())

    }

    @Test
    fun testEmptyList() = runBlocking {
        assertTrue(emptyList<Nothing>().asReceiveChannel().toList().isEmpty())
    }

    @Test
    fun testToList() = runBlocking {
        assertEquals(testList, testList.asReceiveChannel().toList())

    }

    @Test
    fun testEmptySet() = runBlocking {
        assertTrue(emptyList<Nothing>().asReceiveChannel().toSet().isEmpty())

    }

    @Test
    fun testToSet() = runBlocking {
        assertEquals(testList.toSet(), testList.asReceiveChannel().toSet())
    }

    @Test
    fun testEmptySequence() = runBlocking {
        val channel = Channel<Nothing>()
        channel.close()

        assertTrue(emptyList<Nothing>().asReceiveChannel().count() == 0)
    }

    @Test
    fun testEmptyMap() = runBlocking {
        val channel = Channel<Pair<Nothing, Nothing>>()
        channel.close()

        assertTrue(channel.toMap().isEmpty())
    }

    @Test
    fun testToMap() = runBlocking {
        val values = testList.map { it to it.toString() }
        assertEquals(values.toMap(), values.asReceiveChannel().toMap())
    }

    @Test
    fun testReduce() = runBlocking {
        assertEquals(testList.reduce { acc, e -> acc * e }, testList.asReceiveChannel().reduce { acc, e -> acc * e })
    }

    @Test
    fun testTake() = runBlocking {
        for (i in 0..testList.size) {
            assertEquals(testList.take(i), testList.asReceiveChannel().take(i).toList())
        }
    }

    @Test
    fun testPartition() = runBlocking {
        assertEquals(testList.partition { it % 2 == 0 }, testList.asReceiveChannel().partition { it % 2 == 0 })
    }

    @Test
    fun testSendTo() = runBlocking {
        val other = mutableListOf<Int>()
        testList.asReceiveChannel().sendTo(other.asSendChannel())
        assertEquals(testList, other)
    }

    @Test
    fun testZip() = runBlocking {
        val other = listOf("a", "b")
        assertEquals(testList.zip(other), testList.asReceiveChannel().zip(other.asReceiveChannel()).toList())
    }
}
