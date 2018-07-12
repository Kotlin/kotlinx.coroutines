/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.math.*
import kotlin.test.*

class ChannelsTest: TestBase() {
    private val testList = listOf(1, 2, 3)

    @Test
    fun testIterableAsReceiveChannel() = runTest {
        assertEquals(testList, testList.asReceiveChannel().toList())
    }

    @Test
    fun testSequenceAsReceiveChannel() = runTest {
        assertEquals(testList, testList.asSequence().asReceiveChannel().toList())
    }

    @Test
    fun testAssociate() = runTest {
        assertEquals(testList.associate { it * 2 to it * 3 },
            testList.asReceiveChannel().associate { it * 2 to it * 3 }.toMap())
    }

    @Test
    fun testAssociateBy() = runTest {
        assertEquals(testList.associateBy { it % 2 }, testList.asReceiveChannel().associateBy { it % 2 })
    }

    @Test
    fun testAssociateBy2() = runTest {
        assertEquals(testList.associateBy({ it * 2}, { it * 3 }),
            testList.asReceiveChannel().associateBy({ it * 2}, { it * 3 }).toMap())
    }

    @Test
    fun testDistinct() = runTest {
        assertEquals(testList.map { it % 2 }.distinct(), testList.asReceiveChannel().map { it % 2 }.distinct().toList())
    }

    @Test
    fun testDistinctBy() = runTest {
        assertEquals(testList.distinctBy { it % 2 }.toList(), testList.asReceiveChannel().distinctBy { it % 2 }.toList())
    }

    @Test
    fun testToCollection() = runTest {
        val target = mutableListOf<Int>()
        testList.asReceiveChannel().toCollection(target)
        assertEquals(testList, target)
    }

    @Test
    fun testDrop() = runTest {
        for (i in 0..testList.size) {
            assertEquals(testList.drop(i), testList.asReceiveChannel().drop(i).toList(), "Drop $i")
        }
    }

    @Test
    fun testElementAtOrElse() = runTest {
        assertEquals(testList.elementAtOrElse(2) { 42 }, testList.asReceiveChannel().elementAtOrElse(2) { 42 })
        assertEquals(testList.elementAtOrElse(9) { 42 }, testList.asReceiveChannel().elementAtOrElse(9) { 42 })
    }

    @Test
    fun testFirst() = runTest {
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
    fun testFirstOrNull() = runTest {
        assertEquals(testList.firstOrNull(), testList.asReceiveChannel().firstOrNull())
        assertEquals(testList.firstOrNull { it == 2 }, testList.asReceiveChannel().firstOrNull { it == 2 })
        assertEquals(testList.firstOrNull { it == 9 }, testList.asReceiveChannel().firstOrNull { it == 9 })
    }

    @Test
    fun testFlatMap() = runTest {
        assertEquals(testList.flatMap { (0..it).toList() }, testList.asReceiveChannel().flatMap { (0..it).asReceiveChannel() }.toList())

    }

    @Test
    fun testFold() = runTest {
        assertEquals(testList.fold(mutableListOf(42)) { acc, e -> acc.apply { add(e) } },
            testList.asReceiveChannel().fold(mutableListOf(42)) { acc, e -> acc.apply { add(e) } }.toList())
    }

    @Test
    fun testFoldIndexed() = runTest {
        assertEquals(testList.foldIndexed(mutableListOf(42)) { index, acc, e -> acc.apply { add(index + e) } },
            testList.asReceiveChannel().foldIndexed(mutableListOf(42)) { index, acc, e -> acc.apply { add(index + e) } }.toList())
    }

    @Test
    fun testGroupBy() = runTest {
        assertEquals(testList.groupBy { it % 2 }, testList.asReceiveChannel().groupBy { it % 2 })
    }

    @Test
    fun testGroupBy2() = runTest {
        assertEquals(testList.groupBy({ -it }, { it + 100 }), testList.asReceiveChannel().groupBy({ -it }, { it + 100 }).toMap())

    }

    @Test
    fun testMap() = runTest {
        assertEquals(testList.map { it + 10 }, testList.asReceiveChannel().map { it + 10 }.toList())

    }

    @Test
    fun testMapToCollection() = runTest {
        val c = mutableListOf<Int>()
        testList.asReceiveChannel().mapTo(c) { it + 10 }
        assertEquals(testList.map { it + 10 }, c)
    }

    @Test
    fun testMapToSendChannel() = runTest {
        val c = produce<Int>(coroutineContext) {
            testList.asReceiveChannel().mapTo(channel) { it + 10 }
        }
        assertEquals(testList.map { it + 10 }, c.toList())
    }

    @Test
    fun testEmptyList() = runTest {
        assertTrue(emptyList<Nothing>().asReceiveChannel().toList().isEmpty())
    }

    @Test
    fun testToList() = runTest {
        assertEquals(testList, testList.asReceiveChannel().toList())

    }

    @Test
    fun testEmptySet() = runTest {
        assertTrue(emptyList<Nothing>().asReceiveChannel().toSet().isEmpty())

    }

    @Test
    fun testToSet() = runTest {
        assertEquals(testList.toSet(), testList.asReceiveChannel().toSet())
    }

    @Test
    fun testToMutableSet() = runTest {
        assertEquals(testList.toMutableSet(), testList.asReceiveChannel().toMutableSet())
    }

    @Test
    fun testEmptySequence() = runTest {
        val channel = Channel<Nothing>()
        channel.close()

        assertTrue(emptyList<Nothing>().asReceiveChannel().count() == 0)
    }

    @Test
    fun testEmptyMap() = runTest {
        val channel = Channel<Pair<Nothing, Nothing>>()
        channel.close()

        assertTrue(channel.toMap().isEmpty())
    }

    @Test
    fun testToMap() = runTest {
        val values = testList.map { it to it.toString() }
        assertEquals(values.toMap(), values.asReceiveChannel().toMap())
    }

    @Test
    fun testReduce() = runTest {
        assertEquals(testList.reduce { acc, e -> acc * e },
            testList.asReceiveChannel().reduce { acc, e -> acc * e })
    }

    @Test
    fun testReduceIndexed() = runTest {
        assertEquals(testList.reduceIndexed { index, acc, e -> index + acc * e },
            testList.asReceiveChannel().reduceIndexed { index, acc, e -> index + acc * e })
    }

    @Test
    fun testTake() = runTest {
        for (i in 0..testList.size) {
            assertEquals(testList.take(i), testList.asReceiveChannel().take(i).toList())
        }
    }

    @Test
    fun testPartition() = runTest {
        assertEquals(testList.partition { it % 2 == 0 }, testList.asReceiveChannel().partition { it % 2 == 0 })
    }

    @Test
    fun testZip() = runTest {
        val other = listOf("a", "b")
        assertEquals(testList.zip(other), testList.asReceiveChannel().zip(other.asReceiveChannel()).toList())
    }

    @Test
    fun testElementAt() = runTest {
        testList.indices.forEach { i ->
            assertEquals(testList[i], testList.asReceiveChannel().elementAt(i))
        }
    }

    @Test
    fun testElementAtOrNull() = runTest {
        testList.indices.forEach { i ->
            assertEquals(testList[i], testList.asReceiveChannel().elementAtOrNull(i))
        }
        assertEquals(null, testList.asReceiveChannel().elementAtOrNull(-1))
        assertEquals(null, testList.asReceiveChannel().elementAtOrNull(testList.size))
    }

    @Test
    fun testFind() = runTest {
        repeat(3) { mod ->
            assertEquals(testList.find { it % 2 == mod },
                testList.asReceiveChannel().find { it % 2 == mod })
        }
    }

    @Test
    fun testFindLast() = runTest {
        repeat(3) { mod ->
            assertEquals(testList.findLast { it % 2 == mod }, testList.asReceiveChannel().findLast { it % 2 == mod })
        }
    }

    @Test
    fun testIndexOf() = runTest {
        repeat(testList.size + 1) { i ->
            assertEquals(testList.indexOf(i), testList.asReceiveChannel().indexOf(i))
        }
    }

    @Test
    fun testLastIndexOf() = runTest {
        repeat(testList.size + 1) { i ->
            assertEquals(testList.lastIndexOf(i), testList.asReceiveChannel().lastIndexOf(i))
        }
    }

    @Test
    fun testIndexOfFirst() = runTest {
        repeat(3) { mod ->
            assertEquals(testList.indexOfFirst { it % 2 == mod },
                testList.asReceiveChannel().indexOfFirst { it % 2 == mod })
        }
    }

    @Test
    fun testIndexOfLast() = runTest {
        repeat(3) { mod ->
            assertEquals(testList.indexOfLast { it % 2 != mod },
                testList.asReceiveChannel().indexOfLast { it % 2 != mod })
        }
    }

    @Test
    fun testLastOrNull() = runTest {
        assertEquals(testList.lastOrNull(), testList.asReceiveChannel().lastOrNull())
        assertEquals(null, emptyList<Int>().asReceiveChannel().lastOrNull())
    }

    @Test
    fun testSingleOrNull() = runTest {
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
    fun testDropWhile() = runTest {
        repeat(3) { mod ->
            assertEquals(testList.dropWhile { it % 2 == mod },
                testList.asReceiveChannel().dropWhile { it % 2 == mod }.toList())
        }
    }

    @Test
    fun testFilter() = runTest {
        repeat(3) { mod ->
            assertEquals(testList.filter { it % 2 == mod },
                testList.asReceiveChannel().filter { it % 2 == mod }.toList())
        }
    }

    @Test
    fun testFilterToCollection() = runTest {
        repeat(3) { mod ->
            val c = mutableListOf<Int>()
            testList.asReceiveChannel().filterTo(c) { it % 2 == mod }
            assertEquals(testList.filter { it % 2 == mod }, c)
        }
    }

    @Test
    fun testFilterToSendChannel() = runTest {
        repeat(3) { mod ->
            val c = produce<Int>(coroutineContext) {
                testList.asReceiveChannel().filterTo(channel) { it % 2 == mod }
            }
            assertEquals(testList.filter { it % 2 == mod }, c.toList())
        }
    }

    @Test
    fun testFilterNot() = runTest {
        repeat(3) { mod ->
            assertEquals(testList.filterNot { it % 2 == mod },
                testList.asReceiveChannel().filterNot { it % 2 == mod }.toList())
        }
    }

    @Test
    fun testFilterNotToCollection() = runTest {
        repeat(3) { mod ->
            val c = mutableListOf<Int>()
            testList.asReceiveChannel().filterNotTo(c) { it % 2 == mod }
            assertEquals(testList.filterNot { it % 2 == mod }, c)
        }
    }

    @Test
    fun testFilterNotToSendChannel() = runTest {
        repeat(3) { mod ->
            val c = produce<Int>(coroutineContext) {
                testList.asReceiveChannel().filterNotTo(channel) { it % 2 == mod }
            }
            assertEquals(testList.filterNot { it % 2 == mod }, c.toList())
        }
    }

    @Test
    fun testFilterNotNull() = runTest {
        repeat(3) { mod ->
            assertEquals(testList.map { it.takeIf { it % 2 == mod } }.filterNotNull(),
                testList.asReceiveChannel().map { it.takeIf { it % 2 == mod } }.filterNotNull().toList())
        }
    }

    @Test
    fun testFilterNotNullToCollection() = runTest {
        repeat(3) { mod ->
            val c = mutableListOf<Int>()
            testList.asReceiveChannel().map { it.takeIf { it % 2 == mod } }.filterNotNullTo(c)
            assertEquals(testList.map { it.takeIf { it % 2 == mod } }.filterNotNull(), c)
        }
    }

    @Test
    fun testFilterNotNullToSendChannel() = runTest {
        repeat(3) { mod ->
            val c = produce<Int>(coroutineContext) {
                testList.asReceiveChannel().map { it.takeIf { it % 2 == mod } }.filterNotNullTo(channel)
            }
            assertEquals(testList.map { it.takeIf { it % 2 == mod } }.filterNotNull(), c.toList())
        }
    }

    @Test
    fun testFilterIndexed() = runTest {
        repeat(3) { mod ->
            assertEquals(testList.filterIndexed { index, _ ->  index % 2 == mod },
                testList.asReceiveChannel().filterIndexed { index, _ ->  index % 2 == mod }.toList())
        }
    }

    @Test
    fun testFilterIndexedToCollection() = runTest {
        repeat(3) { mod ->
            val c = mutableListOf<Int>()
            testList.asReceiveChannel().filterIndexedTo(c) { index, _ ->  index % 2 == mod }
            assertEquals(testList.filterIndexed { index, _ ->  index % 2 == mod }, c)
        }
    }

    @Test
    fun testFilterIndexedToChannel() = runTest {
        repeat(3) { mod ->
            val c = produce<Int>(coroutineContext) {
                testList.asReceiveChannel().filterIndexedTo(channel) { index, _ -> index % 2 == mod }
            }
            assertEquals(testList.filterIndexed { index, _ ->  index % 2 == mod }, c.toList())
        }
    }

    @Test
    fun testTakeWhile() = runTest {
        repeat(3) { mod ->
            assertEquals(testList.takeWhile { it % 2 != mod },
                testList.asReceiveChannel().takeWhile { it % 2 != mod }.toList())
        }
    }

    @Test
    fun testToChannel() = runTest {
        val c = produce<Int>(coroutineContext) {
            testList.asReceiveChannel().toChannel(channel)
        }
        assertEquals(testList, c.toList())
    }

    @Test
    fun testMapIndexed() = runTest {
        assertEquals(testList.mapIndexed { index, i -> index + i },
            testList.asReceiveChannel().mapIndexed { index, i -> index + i }.toList())
    }

    @Test
    fun testMapIndexedToCollection() = runTest {
        val c = mutableListOf<Int>()
        testList.asReceiveChannel().mapIndexedTo(c) { index, i -> index + i }
        assertEquals(testList.mapIndexed { index, i -> index + i }, c)
    }

    @Test
    fun testMapIndexedToSendChannel() = runTest {
        val c = produce<Int>(coroutineContext) {
            testList.asReceiveChannel().mapIndexedTo(channel) { index, i -> index + i }
        }
        assertEquals(testList.mapIndexed { index, i -> index + i }, c.toList())
    }

    @Test
    fun testMapNotNull() = runTest {
        repeat(3) { mod ->
            assertEquals(testList.mapNotNull { i -> i.takeIf { i % 2 == mod } },
                testList.asReceiveChannel().mapNotNull { i -> i.takeIf { i % 2 == mod } }.toList())
        }
    }

    @Test
    fun testMapNotNullToCollection() = runTest {
        repeat(3) { mod ->
            val c = mutableListOf<Int>()
            testList.asReceiveChannel().mapNotNullTo(c) { i -> i.takeIf { i % 2 == mod } }
            assertEquals(testList.mapNotNull { i -> i.takeIf { i % 2 == mod } }, c)
        }
    }

    @Test
    fun testMapNotNullToSendChannel() = runTest {
        repeat(3) { mod ->
            val c = produce<Int>(coroutineContext) {
                testList.asReceiveChannel().mapNotNullTo(channel) { i -> i.takeIf { i % 2 == mod } }
            }
            assertEquals(testList.mapNotNull { i -> i.takeIf { i % 2 == mod } }, c.toList())
        }
    }

    @Test
    fun testMapIndexedNotNull() = runTest {
        repeat(3) { mod ->
            assertEquals(testList.mapIndexedNotNull { index, i -> index.takeIf { i % 2 == mod } },
                testList.asReceiveChannel().mapIndexedNotNull { index, i -> index.takeIf { i % 2 == mod } }.toList())
        }
    }

    @Test
    fun testMapIndexedNotNullToCollection() = runTest {
        repeat(3) { mod ->
            val c = mutableListOf<Int>()
            testList.asReceiveChannel().mapIndexedNotNullTo(c) { index, i -> index.takeIf { i % 2 == mod } }
            assertEquals(testList.mapIndexedNotNull { index, i -> index.takeIf { i % 2 == mod } }, c)
        }
    }

    @Test
    fun testMapIndexedNotNullToSendChannel() = runTest {
        repeat(3) { mod ->
            val c = produce<Int>(coroutineContext) {
                testList.asReceiveChannel().mapIndexedNotNullTo(channel) { index, i -> index.takeIf { i % 2 == mod } }
            }
            assertEquals(testList.mapIndexedNotNull { index, i -> index.takeIf { i % 2 == mod } }, c.toList())
        }
    }

    @Test
    fun testWithIndex() = runTest {
        assertEquals(testList.withIndex().toList(), testList.asReceiveChannel().withIndex().toList())
    }

    @Test
    fun testMaxBy() = runTest {
        assertEquals(testList.maxBy { 10 - abs(it - 2) },
            testList.asReceiveChannel().maxBy { 10 - abs(it - 2) })
    }

    @Test
    fun testMaxWith() = runTest {
        val cmp = compareBy<Int> { 10 - abs(it - 2) }
        assertEquals(testList.maxWith(cmp),
            testList.asReceiveChannel().maxWith(cmp))
    }

    @Test
    fun testMinBy() = runTest {
        assertEquals(testList.minBy { abs(it - 2) },
            testList.asReceiveChannel().minBy { abs(it - 2) })
    }

    @Test
    fun testMinWith() = runTest {
        val cmp = compareBy<Int> { abs(it - 2) }
        assertEquals(testList.minWith(cmp),
            testList.asReceiveChannel().minWith(cmp))
    }

    @Test
    fun testSumBy() = runTest {
        assertEquals(testList.sumBy { it * 3 },
            testList.asReceiveChannel().sumBy { it * 3 })
    }

    @Test
    fun testSumByDouble() = runTest {
        val expected = testList.sumByDouble { it * 3.0 }
        val actual = testList.asReceiveChannel().sumByDouble { it * 3.0 }
        assertEquals(expected, actual)
    }

    @Test
    fun testRequireNoNulls() = runTest {
        assertEquals(testList.requireNoNulls(), testList.asReceiveChannel().requireNoNulls().toList())
    }
}
