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

import kotlinx.coroutines.experimental.async
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Assert.*
import org.junit.Test

class ChannelsTest {
    private val testList = listOf(1, 2, 3)

    @Test
    fun testBlocking() {
        val ch = Channel<Int>()
        val sum = async {
            ch.sumBy { it }
        }
        repeat(10) {
            ch.sendBlocking(it)
        }
        ch.close()
        assertEquals(45, runBlocking { sum.await() })

    }

    @Test
    fun testIterableAsReceiveChannel() = runBlocking {
        assertEquals(testList, testList.asReceiveChannel().toList())
    }

    @Test
    fun testSequenceAsReceiveChannel() = runBlocking {
        assertEquals(testList, testList.asSequence().asReceiveChannel().toList())
    }

    @Test
    fun testAssociate() = runBlocking {
        assertEquals(testList.associate { it * 2 to it * 3 },
            testList.asReceiveChannel().associate { it * 2 to it * 3 }.toMap())
    }

    @Test
    fun testAssociateBy() = runBlocking {
        assertEquals(testList.associateBy { it % 2 }, testList.asReceiveChannel().associateBy { it % 2 })
    }

    @Test
    fun testAssociateBy2() = runBlocking {
        assertEquals(testList.associateBy({ it * 2}, { it * 3 }),
            testList.asReceiveChannel().associateBy({ it * 2}, { it * 3 }).toMap())
    }

    @Test
    fun testDistinct() = runBlocking {
        assertEquals(testList.map { it % 2 }.distinct(), testList.asReceiveChannel().map { it % 2 }.distinct().toList())
    }

    @Test
    fun testDistinctBy() = runBlocking {
        assertEquals(testList.distinctBy { it % 2 }.toList(), testList.asReceiveChannel().distinctBy { it % 2 }.toList())
    }

    @Test
    fun testToCollection() = runBlocking {
        val target = mutableListOf<Int>()
        testList.asReceiveChannel().toCollection(target)
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
        assertEquals(testList.first(), testList.asReceiveChannel().first())
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
        assertEquals(testList.firstOrNull(), testList.asReceiveChannel().firstOrNull())
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
    fun testFoldIndexed() = runBlocking {
        assertEquals(testList.foldIndexed(mutableListOf(42)) { index, acc, e -> acc.apply { add(index + e) } },
            testList.asReceiveChannel().foldIndexed(mutableListOf(42)) { index, acc, e -> acc.apply { add(index + e) } }.toList())
    }

    @Test
    fun testGroupBy() = runBlocking {
        assertEquals(testList.groupBy { it % 2 }, testList.asReceiveChannel().groupBy { it % 2 })
    }

    @Test
    fun testGroupBy2() = runBlocking {
        assertEquals(testList.groupBy({ -it }, { it + 100 }), testList.asReceiveChannel().groupBy({ -it }, { it + 100 }).toMap())

    }

    @Test
    fun testMap() = runBlocking {
        assertEquals(testList.map { it + 10 }, testList.asReceiveChannel().map { it + 10 }.toList())

    }

    @Test
    fun testMapToCollection() = runBlocking {
        val c = mutableListOf<Int>()
        testList.asReceiveChannel().mapTo(c) { it + 10 }
        assertEquals(testList.map { it + 10 }, c)
    }

    @Test
    fun testMapToSendChannel() = runBlocking {
        val c = produce<Int> {
            testList.asReceiveChannel().mapTo(channel) { it + 10 }
        }
        assertEquals(testList.map { it + 10 }, c.toList())
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
    fun testToMutableSet() = runBlocking {
        assertEquals(testList.toMutableSet(), testList.asReceiveChannel().toMutableSet())
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
        assertEquals(testList.reduce { acc, e -> acc * e },
            testList.asReceiveChannel().reduce { acc, e -> acc * e })
    }

    @Test
    fun testReduceIndexed() = runBlocking {
        assertEquals(testList.reduceIndexed { index, acc, e -> index + acc * e },
            testList.asReceiveChannel().reduceIndexed { index, acc, e -> index + acc * e })
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
    fun testZip() = runBlocking {
        val other = listOf("a", "b")
        assertEquals(testList.zip(other), testList.asReceiveChannel().zip(other.asReceiveChannel()).toList())
    }

    @Test
    fun testElementAt() = runBlocking {
        testList.indices.forEach { i ->
            assertEquals(testList[i], testList.asReceiveChannel().elementAt(i))
        }
    }

    @Test
    fun testElementAtOrNull() = runBlocking {
        testList.indices.forEach { i ->
            assertEquals(testList[i], testList.asReceiveChannel().elementAtOrNull(i))
        }
        assertEquals(null, testList.asReceiveChannel().elementAtOrNull(-1))
        assertEquals(null, testList.asReceiveChannel().elementAtOrNull(testList.size))
    }

    @Test
    fun testFind() = runBlocking {
        repeat(3) { mod ->
            assertEquals(testList.find { it % 2 == mod },
                testList.asReceiveChannel().find { it % 2 == mod })
        }
    }

    @Test
    fun testFindLast() = runBlocking {
        repeat(3) { mod ->
            assertEquals(testList.findLast { it % 2 == mod }, testList.asReceiveChannel().findLast { it % 2 == mod })
        }
    }

    @Test
    fun testIndexOf() = runBlocking {
        repeat(testList.size + 1) { i ->
            assertEquals(testList.indexOf(i), testList.asReceiveChannel().indexOf(i))
        }
    }

    @Test
    fun testLastIndexOf() = runBlocking {
        repeat(testList.size + 1) { i ->
            assertEquals(testList.lastIndexOf(i), testList.asReceiveChannel().lastIndexOf(i))
        }
    }

    @Test
    fun testIndexOfFirst() = runBlocking {
        repeat(3) { mod ->
            assertEquals(testList.indexOfFirst { it % 2 == mod },
                testList.asReceiveChannel().indexOfFirst { it % 2 == mod })
        }
    }

    @Test
    fun testIndexOfLast() = runBlocking {
        repeat(3) { mod ->
            assertEquals(testList.indexOfLast { it % 2 != mod },
                testList.asReceiveChannel().indexOfLast { it % 2 != mod })
        }
    }

    @Test
    fun testLastOrNull() = runBlocking {
        assertEquals(testList.lastOrNull(), testList.asReceiveChannel().lastOrNull())
        assertEquals(null, emptyList<Int>().asReceiveChannel().lastOrNull())
    }

    @Test
    fun testSingleOrNull() = runBlocking {
        assertEquals(1, listOf(1).asReceiveChannel().singleOrNull())
        assertEquals(null, listOf(1, 2).asReceiveChannel().singleOrNull())
        assertEquals(null, emptyList<Int>().asReceiveChannel().singleOrNull())
        repeat(testList.size + 1) { i ->
            assertEquals(testList.singleOrNull { it == i },
                testList.asReceiveChannel().singleOrNull { it == i })
        }
        repeat(3) { mod ->
            assertEquals(testList.singleOrNull { it % 2 == mod },
                testList.asReceiveChannel().singleOrNull { it % 2 == mod })
        }
    }

    @Test
    fun testDropWhile() = runBlocking {
        repeat(3) { mod ->
            assertEquals(testList.dropWhile { it % 2 == mod },
                testList.asReceiveChannel().dropWhile { it % 2 == mod }.toList())
        }
    }

    @Test
    fun testFilter() = runBlocking {
        repeat(3) { mod ->
            assertEquals(testList.filter { it % 2 == mod },
                testList.asReceiveChannel().filter { it % 2 == mod }.toList())
        }
    }

    @Test
    fun testFilterToCollection() = runBlocking {
        repeat(3) { mod ->
            val c = mutableListOf<Int>()
            testList.asReceiveChannel().filterTo(c) { it % 2 == mod }
            assertEquals(testList.filter { it % 2 == mod }, c)
        }
    }

    @Test
    fun testFilterToSendChannel() = runBlocking {
        repeat(3) { mod ->
            val c = produce<Int> {
                testList.asReceiveChannel().filterTo(channel) { it % 2 == mod }
            }
            assertEquals(testList.filter { it % 2 == mod }, c.toList())
        }
    }

    @Test
    fun testFilterNot() = runBlocking {
        repeat(3) { mod ->
            assertEquals(testList.filterNot { it % 2 == mod },
                testList.asReceiveChannel().filterNot { it % 2 == mod }.toList())
        }
    }

    @Test
    fun testFilterNotToCollection() = runBlocking {
        repeat(3) { mod ->
            val c = mutableListOf<Int>()
            testList.asReceiveChannel().filterNotTo(c) { it % 2 == mod }
            assertEquals(testList.filterNot { it % 2 == mod }, c)
        }
    }

    @Test
    fun testFilterNotToSendChannel() = runBlocking {
        repeat(3) { mod ->
            val c = produce<Int> {
                testList.asReceiveChannel().filterNotTo(channel) { it % 2 == mod }
            }
            assertEquals(testList.filterNot { it % 2 == mod }, c.toList())
        }
    }

    @Test
    fun testFilterNotNull() = runBlocking {
        repeat(3) { mod ->
            assertEquals(testList.map { it.takeIf { it % 2 == mod } }.filterNotNull(),
                testList.asReceiveChannel().map { it.takeIf { it % 2 == mod } }.filterNotNull().toList())
        }
    }

    @Test
    fun testFilterNotNullToCollection() = runBlocking {
        repeat(3) { mod ->
            val c = mutableListOf<Int>()
            testList.asReceiveChannel().map { it.takeIf { it % 2 == mod } }.filterNotNullTo(c)
            assertEquals(testList.map { it.takeIf { it % 2 == mod } }.filterNotNull(), c)
        }
    }

    @Test
    fun testFilterNotNullToSendChannel() = runBlocking {
        repeat(3) { mod ->
            val c = produce<Int> {
                testList.asReceiveChannel().map { it.takeIf { it % 2 == mod } }.filterNotNullTo(channel)
            }
            assertEquals(testList.map { it.takeIf { it % 2 == mod } }.filterNotNull(), c.toList())
        }
    }

    @Test
    fun testFilterIndexed() = runBlocking {
        repeat(3) { mod ->
            assertEquals(testList.filterIndexed { index, _ ->  index % 2 == mod },
                testList.asReceiveChannel().filterIndexed { index, _ ->  index % 2 == mod }.toList())
        }
    }

    @Test
    fun testFilterIndexedToCollection() = runBlocking {
        repeat(3) { mod ->
            val c = mutableListOf<Int>()
            testList.asReceiveChannel().filterIndexedTo(c) { index, _ ->  index % 2 == mod }
            assertEquals(testList.filterIndexed { index, _ ->  index % 2 == mod }, c)
        }
    }

    @Test
    fun testFilterIndexedToChannel() = runBlocking {
        repeat(3) { mod ->
            val c = produce<Int> {
                testList.asReceiveChannel().filterIndexedTo(channel) { index, _ ->  index % 2 == mod }
            }
            assertEquals(testList.filterIndexed { index, _ ->  index % 2 == mod }, c.toList())
        }
    }

    @Test
    fun testTakeWhile() = runBlocking {
        repeat(3) { mod ->
            assertEquals(testList.takeWhile { it % 2 != mod },
                testList.asReceiveChannel().takeWhile { it % 2 != mod }.toList())
        }
    }

    @Test
    fun testToChannel() = runBlocking {
        val c = produce<Int> {
            testList.asReceiveChannel().toChannel(channel)
        }
        assertEquals(testList, c.toList())
    }

    @Test
    fun testMapIndexed() = runBlocking {
        assertEquals(testList.mapIndexed { index, i -> index + i },
            testList.asReceiveChannel().mapIndexed { index, i -> index + i }.toList())
    }

    @Test
    fun testMapIndexedToCollection() = runBlocking {
        val c = mutableListOf<Int>()
        testList.asReceiveChannel().mapIndexedTo(c) { index, i -> index + i }
        assertEquals(testList.mapIndexed { index, i -> index + i }, c)
    }

    @Test
    fun testMapIndexedToSendChannel() = runBlocking {
        val c = produce<Int> {
            testList.asReceiveChannel().mapIndexedTo(channel) { index, i -> index + i }
        }
        assertEquals(testList.mapIndexed { index, i -> index + i }, c.toList())
    }

    @Test
    fun testMapNotNull() = runBlocking {
        repeat(3) { mod ->
            assertEquals(testList.mapNotNull { i -> i.takeIf { i % 2 == mod } },
                testList.asReceiveChannel().mapNotNull { i -> i.takeIf { i % 2 == mod } }.toList())
        }
    }

    @Test
    fun testMapNotNullToCollection() = runBlocking {
        repeat(3) { mod ->
            val c = mutableListOf<Int>()
            testList.asReceiveChannel().mapNotNullTo(c) { i -> i.takeIf { i % 2 == mod } }
            assertEquals(testList.mapNotNull { i -> i.takeIf { i % 2 == mod } }, c)
        }
    }

    @Test
    fun testMapNotNullToSendChannel() = runBlocking {
        repeat(3) { mod ->
            val c = produce<Int> {
                testList.asReceiveChannel().mapNotNullTo(channel) { i -> i.takeIf { i % 2 == mod } }
            }
            assertEquals(testList.mapNotNull { i -> i.takeIf { i % 2 == mod } }, c.toList())
        }
    }

    @Test
    fun testMapIndexedNotNull() = runBlocking {
        repeat(3) { mod ->
            assertEquals(testList.mapIndexedNotNull { index, i -> index.takeIf { i % 2 == mod } },
                testList.asReceiveChannel().mapIndexedNotNull { index, i -> index.takeIf { i % 2 == mod } }.toList())
        }
    }

    @Test
    fun testMapIndexedNotNullToCollection() = runBlocking {
        repeat(3) { mod ->
            val c = mutableListOf<Int>()
            testList.asReceiveChannel().mapIndexedNotNullTo(c) { index, i -> index.takeIf { i % 2 == mod } }
            assertEquals(testList.mapIndexedNotNull { index, i -> index.takeIf { i % 2 == mod } }, c)
        }
    }

    @Test
    fun testMapIndexedNotNullToSendChannel() = runBlocking {
        repeat(3) { mod ->
            val c = produce<Int> {
                testList.asReceiveChannel().mapIndexedNotNullTo(channel) { index, i -> index.takeIf { i % 2 == mod } }
            }
            assertEquals(testList.mapIndexedNotNull { index, i -> index.takeIf { i % 2 == mod } }, c.toList())
        }
    }

    @Test
    fun testWithIndex() = runBlocking {
        assertEquals(testList.withIndex().toList(), testList.asReceiveChannel().withIndex().toList())
    }

    @Test
    fun testMaxBy() = runBlocking {
        assertEquals(testList.maxBy { 10 - Math.abs(it - 2) },
            testList.asReceiveChannel().maxBy { 10 - Math.abs(it - 2) })
    }

    @Test
    fun testMaxWith() = runBlocking {
        val cmp = compareBy<Int> { 10 - Math.abs(it - 2) }
        assertEquals(testList.maxWith(cmp),
            testList.asReceiveChannel().maxWith(cmp))
    }

    @Test
    fun testMinBy() = runBlocking {
        assertEquals(testList.minBy { Math.abs(it - 2) },
            testList.asReceiveChannel().minBy { Math.abs(it - 2) })
    }

    @Test
    fun testMinWith() = runBlocking {
        val cmp = compareBy<Int> { Math.abs(it - 2) }
        assertEquals(testList.minWith(cmp),
            testList.asReceiveChannel().minWith(cmp))
    }

    @Test
    fun testSumBy() = runBlocking {
        assertEquals(testList.sumBy { it * 3 },
            testList.asReceiveChannel().sumBy { it * 3 })
    }

    @Test
    fun testSumByDouble() = runBlocking {
        assertEquals(testList.sumByDouble { it * 3.0 },
            testList.asReceiveChannel().sumByDouble { it * 3.0 }, 1e-10)
    }

    @Test
    fun testRequireNoNulls() = runBlocking {
        assertEquals(testList.requireNoNulls(), testList.asReceiveChannel().requireNoNulls().toList())
    }
}
