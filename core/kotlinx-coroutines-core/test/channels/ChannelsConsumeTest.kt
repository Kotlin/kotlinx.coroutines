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

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

/**
 * Tests that various operators on channels properly consume (close) their source channels.
 */
class ChannelsConsumeTest {
    private val sourceList = (1..10).toList()

    // test source with numbers 1..10
    private fun testSource(context: CoroutineContext) = produce(context) {
        for (i in sourceList) {
            send(i)
        }
    }

    @Test
    fun testConsume() {
        checkTerminal {
            consume {
                assertEquals(1, receive())
            }
        }
    }

    @Test
    fun testConsumeEach() {
        checkTerminal {
            var sum = 0
            consumeEach { sum += it }
            assertEquals(55, sum)
        }
    }

    @Test
    fun testConsumeEachIndexed() {
        checkTerminal {
            var sum = 0
            consumeEachIndexed { (index, i) -> sum += index * i }
            assertEquals(330, sum)
        }
    }

    @Test
    fun testElementAt() {
        checkTerminal {
            assertEquals(2, elementAt(1))
        }
        checkTerminal(expected = { it is IndexOutOfBoundsException }) {
            elementAt(10)
        }
    }

    @Test
    fun testElementAtOrElse() {
        checkTerminal {
            assertEquals(3, elementAtOrElse(2) { error("Cannot happen") })
        }
        checkTerminal {
            assertEquals(-23, elementAtOrElse(10) { -23 })
        }
    }

    @Test
    fun testElementOrNull() {
        checkTerminal {
            assertEquals(4, elementAtOrNull(3))
        }
        checkTerminal {
            assertEquals(null, elementAtOrNull(10))
        }
    }

    @Test
    fun testFind() {
        checkTerminal {
            assertEquals(3, find { it % 3 == 0 })
        }
    }

    @Test
    fun testFindLast() {
        checkTerminal {
            assertEquals(9, findLast { it % 3 == 0 })
        }
    }

    @Test
    fun testFirst() {
        checkTerminal {
            assertEquals(1, first())
        }
    }

    @Test
    fun testFirstPredicate() {
        checkTerminal {
            assertEquals(3, first { it % 3 == 0 })
        }
        checkTerminal(expected = { it is NoSuchElementException }) {
            first { it > 10 }
        }
    }

    @Test
    fun testFirstOrNull() {
        checkTerminal {
            assertEquals(1, firstOrNull())
        }
    }

    @Test
    fun testFirstOrNullPredicate() {
        checkTerminal {
            assertEquals(3, firstOrNull { it % 3 == 0 })
        }
        checkTerminal {
            assertEquals(null, firstOrNull { it > 10 })
        }
    }

    @Test
    fun testIndexOf() {
        checkTerminal {
            assertEquals(2, indexOf(3))
        }
        checkTerminal {
            assertEquals(-1, indexOf(11))
        }
    }

    @Test
    fun testIndexOfFirst() {
        checkTerminal {
            assertEquals(2, indexOfFirst { it % 3 == 0 })
        }
        checkTerminal {
            assertEquals(-1, indexOfFirst { it > 10 })
        }
    }

    @Test
    fun testIndexOfLast() {
        checkTerminal {
            assertEquals(8, indexOfLast { it % 3 == 0 })
        }
        checkTerminal {
            assertEquals(-1, indexOfLast { it > 10 })
        }
    }

    @Test
    fun testLast() {
        checkTerminal {
            assertEquals(10, last())
        }
    }

    @Test
    fun testLastPredicate() {
        checkTerminal {
            assertEquals(9, last { it % 3 == 0 })
        }
        checkTerminal(expected = { it is NoSuchElementException }) {
            last { it > 10 }
        }
    }

    @Test
    fun testLastIndexOf() {
        checkTerminal {
            assertEquals(8, lastIndexOf(9))
        }
    }

    @Test
    fun testLastOrNull() {
        checkTerminal {
            assertEquals(10, lastOrNull())
        }
    }

    @Test
    fun testLastOrNullPredicate() {
        checkTerminal {
            assertEquals(9, lastOrNull { it % 3 == 0 })
        }
        checkTerminal {
            assertEquals(null, lastOrNull { it > 10 })
        }
    }

    @Test
    fun testSingle() {
        checkTerminal(expected = { it is IllegalArgumentException }) {
            single()
        }
    }

    @Test
    fun testSinglePredicate() {
        checkTerminal {
            assertEquals(7, single { it % 7 == 0 })
        }
        checkTerminal(expected = { it is IllegalArgumentException }) {
            single { it % 3 == 0 }
        }
        checkTerminal(expected = { it is NoSuchElementException }) {
            single { it > 10 }
        }
    }

    @Test
    fun testSingleOrNull() {
        checkTerminal {
            assertEquals(null, singleOrNull())
        }
    }

    @Test
    fun testSingleOrNullPredicate() {
        checkTerminal {
            assertEquals(7, singleOrNull { it % 7 == 0 })
        }
        checkTerminal {
            assertEquals(null, singleOrNull { it % 3 == 0 })
        }
        checkTerminal {
            assertEquals(null, singleOrNull { it > 10 })
        }
    }

    @Test
    fun testDrop() {
        checkTransform(sourceList.drop(3)) { ctx ->
            drop(3, ctx)
        }
    }

    @Test
    fun testDropWhile() {
        checkTransform(sourceList.dropWhile { it < 4}) { ctx ->
            dropWhile(ctx) { it < 4 }
        }
    }

    @Test
    fun testFilter() {
        checkTransform(sourceList.filter { it % 2 == 0 }) { ctx ->
            filter(ctx) { it % 2 == 0 }
        }
    }

    @Test
    fun testFilterIndexed() {
        checkTransform(sourceList.filterIndexed { index, _ -> index % 2 == 0 }) { ctx ->
            filterIndexed(ctx) { index, _ -> index % 2 == 0 }
        }
    }

    @Test
    fun testFilterIndexedToCollection() {
        checkTerminal {
            val list = mutableListOf<Int>()
            filterIndexedTo(list) { index, _ -> index % 2 == 0 }
            assertEquals(listOf(1, 3, 5, 7, 9), list)
        }
    }

    @Test
    fun testFilterIndexedToChannel() {
        checkTerminal {
            val channel = Channel<Int>()
            val result = async { channel.toList() }
            filterIndexedTo(channel) { index, _ -> index % 2 == 0 }
            channel.close()
            assertEquals(listOf(1, 3, 5, 7, 9), result.await())
        }
    }

    @Test
    fun testFilterNot() {
        checkTransform(sourceList.filterNot { it % 2 == 0 }) { ctx ->
            filterNot(ctx) { it % 2 == 0 }
        }
    }

    @Test
    fun testFilterNotNullToCollection() {
        checkTerminal {
            val list = mutableListOf<Int>()
            filterNotNullTo(list)
            assertEquals((1..10).toList(), list)
        }
    }

    @Test
    fun testFilterNotNullToChannel() {
        checkTerminal {
            val channel = Channel<Int>()
            val result = async { channel.toList() }
            filterNotNullTo(channel)
            channel.close()
            assertEquals((1..10).toList(), result.await())
        }
    }

    @Test
    fun testFilterNotToCollection() {
        checkTerminal {
            val list = mutableListOf<Int>()
            filterNotTo(list) { it % 2 == 0 }
            assertEquals(listOf(1, 3, 5, 7, 9), list)
        }
    }

    @Test
    fun testFilterNotToChannel() {
        checkTerminal {
            val channel = Channel<Int>()
            val result = async { channel.toList() }
            filterNotTo(channel) { it % 2 == 0 }
            channel.close()
            assertEquals(listOf(1, 3, 5, 7, 9), result.await())
        }
    }

    @Test
    fun testFilterToCollection() {
        checkTerminal {
            val list = mutableListOf<Int>()
            filterTo(list) { it % 2 == 0 }
            assertEquals(listOf(2, 4, 6, 8, 10), list)
        }
    }

    @Test
    fun testFilterToChannel() {
        checkTerminal {
            val channel = Channel<Int>()
            val result = async { channel.toList() }
            filterTo(channel) { it % 2 == 0 }
            channel.close()
            assertEquals(listOf(2, 4, 6, 8, 10), result.await())
        }
    }

    @Test
    fun testTake() {
        checkTransform(sourceList.take(3)) { ctx ->
            take(3, ctx)
        }
    }

    @Test
    fun testTakeWhile() {
        checkTransform(sourceList.takeWhile { it < 4 }) { ctx ->
            takeWhile(ctx) { it < 4 }
        }
    }

    @Test
    fun testAssociate() {
        checkTerminal {
            assertEquals(sourceList.associate { it to it.toString() }, associate { it to it.toString() })
        }
    }

    @Test
    fun testAssociateBy() {
        checkTerminal {
            assertEquals(sourceList.associateBy { it.toString() }, associateBy { it.toString() })
        }
    }

    @Test
    fun testAssociateByTwo() {
        checkTerminal {
            assertEquals(sourceList.associateBy({ it.toString() }, { it + 1}), associateBy({ it.toString() }, { it + 1}))
        }
    }

    @Test
    fun testAssociateByToMap() {
        checkTerminal {
            val map = mutableMapOf<String, Int>()
            associateByTo(map) { it.toString() }
            assertEquals(sourceList.associateBy { it.toString() }, map)
        }
    }

    @Test
    fun testAssociateByTwoToMap() {
        checkTerminal {
            val map = mutableMapOf<String, Int>()
            associateByTo(map, { it.toString() }, { it + 1})
            assertEquals(sourceList.associateBy({ it.toString() }, { it + 1}), map)
        }
    }

    @Test
    fun testAssociateToMap() {
        checkTerminal {
            val map = mutableMapOf<Int, String>()
            associateTo(map) { it to it.toString() }
            assertEquals(sourceList.associate { it to it.toString() }, map)
        }
    }

    @Test
    fun testToChannel() {
        checkTerminal {
            val channel = Channel<Int>()
            val result = async { channel.toList() }
            toChannel(channel)
            channel.close()
            assertEquals(sourceList, result.await())
        }
    }

    @Test
    fun testToCollection() {
        checkTerminal {
            val list = mutableListOf<Int>()
            toCollection(list)
            assertEquals(sourceList, list)
        }
    }

    @Test
    fun testToList() {
        checkTerminal {
            val list = toList()
            assertEquals(sourceList, list)
        }
    }

    @Test
    fun testToMap() {
        checkTerminal {
            val map = map { it to it.toString() }.toMap()
            assertEquals(sourceList.map { it to it.toString() }.toMap(), map)
        }
    }

    @Test
    fun testToMapWithMap() {
        checkTerminal {
            val map = mutableMapOf<Int, String>()
            map { it to it.toString() }.toMap(map)
            assertEquals(sourceList.map { it to it.toString() }.toMap(), map)
        }
    }

    @Test
    fun testToMutableList() {
        checkTerminal {
            val list = toMutableList()
            assertEquals(sourceList, list)
        }
    }

    @Test
    fun testToSet() {
        checkTerminal {
            val set = toSet()
            assertEquals(sourceList.toSet(), set)
        }
    }

    @Test
    fun testFlatMap() {
        checkTransform(sourceList.flatMap { listOf("A$it", "B$it") }) { ctx ->
            flatMap(ctx) {
                produce {
                    send("A$it")
                    send("B$it")
                }
            }
        }
    }

    @Test
    fun testGroupBy() {
        checkTerminal {
            val map = groupBy { it % 2 }
            assertEquals(sourceList.groupBy { it % 2 }, map)
        }
    }

    @Test
    fun testGroupByTwo() {
        checkTerminal {
            val map = groupBy({ it % 2 }, { it.toString() })
            assertEquals(sourceList.groupBy({ it % 2 }, { it.toString() }), map)
        }
    }

    @Test
    fun testGroupByTo() {
        checkTerminal {
            val map = mutableMapOf<Int, MutableList<Int>>()
            groupByTo(map) { it % 2 }
            assertEquals(sourceList.groupBy { it % 2 }, map)
        }
    }

    @Test
    fun testGroupByToTwo() {
        checkTerminal {
            val map = mutableMapOf<Int, MutableList<String>>()
            groupByTo(map, { it % 2 }, { it.toString() })
            assertEquals(sourceList.groupBy({ it % 2 }, { it.toString() }), map)
        }
    }

    @Test
    fun testMap() {
        checkTransform(sourceList.map { it.toString() }) { ctx ->
            map(ctx) { it.toString() }
        }
    }

    @Test
    fun testMapIndexed() {
        checkTransform(sourceList.mapIndexed { index, v -> "$index$v" }) { ctx ->
            mapIndexed(ctx) { index, v -> "$index$v" }
        }
    }

    @Test
    fun testMapIndexedNotNull() {
        checkTransform(sourceList.mapIndexedNotNull { index, v -> "$index$v".takeIf { v % 2 == 0 } }) { ctx ->
            mapIndexedNotNull(ctx) { index, v -> "$index$v".takeIf { v % 2 == 0 } }
        }
    }

    @Test
    fun testMapIndexedNotNullToCollection() {
        checkTerminal {
            val list = mutableListOf<String>()
            mapIndexedNotNullTo(list) { index, v -> "$index$v".takeIf { v % 2 == 0 } }
            assertEquals(sourceList.mapIndexedNotNull { index, v -> "$index$v".takeIf { v % 2 == 0 } }, list)
        }
    }

    @Test
    fun testMapIndexedNotNullToChannel() {
        checkTerminal {
            val channel = Channel<String>()
            val result = async { channel.toList() }
            mapIndexedNotNullTo(channel) { index, v -> "$index$v".takeIf { v % 2 == 0 } }
            channel.close()
            assertEquals(sourceList.mapIndexedNotNull { index, v -> "$index$v".takeIf { v % 2 == 0 } }, result.await())
        }
    }

    @Test
    fun testMapIndexedToCollection() {
        checkTerminal {
            val list = mutableListOf<String>()
            mapIndexedTo(list) { index, v -> "$index$v" }
            assertEquals(sourceList.mapIndexed { index, v -> "$index$v" }, list)
        }
    }

    @Test
    fun testMapIndexedToChannel() {
        checkTerminal {
            val channel = Channel<String>()
            val result = async { channel.toList() }
            mapIndexedTo(channel) { index, v -> "$index$v" }
            channel.close()
            assertEquals(sourceList.mapIndexed { index, v -> "$index$v" }, result.await())
        }
    }

    @Test
    fun testMapNotNull() {
        checkTransform(sourceList.mapNotNull { (it + 3).takeIf { it % 2 == 0 } }) { ctx ->
            mapNotNull(ctx) { (it + 3).takeIf { it % 2 == 0 } }
        }
    }

    @Test
    fun testMapNotNullToCollection() {
        checkTerminal {
            val list = mutableListOf<Int>()
            mapNotNullTo(list) { (it + 3).takeIf { it % 2 == 0 } }
            assertEquals(sourceList.mapNotNull { (it + 3).takeIf { it % 2 == 0 } }, list)
        }
    }

    @Test
    fun testMapNotNullToChannel() {
        checkTerminal {
            val channel = Channel<Int>()
            val result = async { channel.toList() }
            mapNotNullTo(channel) { (it + 3).takeIf { it % 2 == 0 } }
            channel.close()
            assertEquals(sourceList.mapNotNull { (it + 3).takeIf { it % 2 == 0 } }, result.await())
        }
    }

    @Test
    fun testMapToCollection() {
        checkTerminal {
            val list = mutableListOf<Int>()
            mapTo(list) { it + 3 }
            assertEquals(sourceList.map { it + 3 }, list)
        }
    }

    @Test
    fun testMapToChannel() {
        checkTerminal {
            val channel = Channel<Int>()
            val result = async { channel.toList() }
            mapTo(channel) { it + 3 }
            channel.close()
            assertEquals(sourceList.map { it + 3 }, result.await())
        }
    }

    @Test
    fun testWithIndex() {
        checkTransform(sourceList.withIndex().toList()) { ctx ->
            withIndex(ctx)
        }
    }

    @Test
    fun testDistinctBy() {
        checkTransform(sourceList.distinctBy { it / 2 }) { ctx ->
            distinctBy(ctx) { it / 2 }
        }
    }

    @Test
    fun testToMutableSet() {
        checkTerminal {
            val set = toMutableSet()
            assertEquals(sourceList.toSet(), set)
        }
    }

    @Test
    fun testAll() {
        checkTerminal {
            val all = all { it < 11 }
            assertEquals(sourceList.all { it < 11 }, all)
        }
    }

    @Test
    fun testAny() {
        checkTerminal {
            val any = any()
            assertEquals(sourceList.any(), any)
        }
    }

    @Test
    fun testAnyPredicate() {
        checkTerminal {
            val any = any { it % 3 == 0 }
            assertEquals(sourceList.any { it % 3 == 0 }, any)
        }
    }
    
    @Test
    fun testCount() {
        checkTerminal {
            val c = count()
            assertEquals(sourceList.count(), c)
        }
    }

    @Test
    fun testCountPredicate() {
        checkTerminal {
            val c = count { it % 3 == 0 }
            assertEquals(sourceList.count { it % 3 == 0 }, c)
        }
    }

    @Test
    fun testFold() {
        checkTerminal {
            val c = fold(1) { a, b -> a + b }
            assertEquals(sourceList.fold(1) { a, b -> a + b }, c)
        }
    }

    @Test
    fun testFoldIndexed() {
        checkTerminal {
            val c = foldIndexed(1) { i, a, b -> i * a + b }
            assertEquals(sourceList.foldIndexed(1) { i, a, b -> i * a + b }, c)
        }
    }

    @Test
    fun testMaxBy() {
        checkTerminal {
            val c = maxBy { it % 3 }
            assertEquals(sourceList.maxBy { it % 3 }, c)
        }
    }

    @Test
    fun testMaxWith() {
        checkTerminal {
            val c = maxWith(compareBy { it % 3 })
            assertEquals(sourceList.maxWith(compareBy { it % 3 }), c)
        }
    }

    @Test
    fun testMinBy() {
        checkTerminal {
            val c = maxBy { it % 3 }
            assertEquals(sourceList.maxBy { it % 3 }, c)
        }
    }

    @Test
    fun testMinWith() {
        checkTerminal {
            val c = maxWith(compareBy { it % 3 })
            assertEquals(sourceList.maxWith(compareBy { it % 3 }), c)
        }
    }

    @Test
    fun testNone() {
        checkTerminal {
            val none = none()
            assertEquals(sourceList.none(), none)
        }
    }

    @Test
    fun testNonePredicate() {
        checkTerminal {
            val none = none { it > 10 }
            assertEquals(sourceList.none { it > 10 }, none)
        }
    }

    @Test
    fun testReduce() {
        checkTerminal {
            val c = reduce { a, b -> a + b }
            assertEquals(sourceList.reduce { a, b -> a + b }, c)
        }
    }

    @Test
    fun testReduceIndexed() {
        checkTerminal {
            val c = reduceIndexed { i, a, b -> i * a + b }
            assertEquals(sourceList.reduceIndexed { i, a, b -> i * a + b }, c)
        }
    }

    @Test
    fun testSubBy() {
        checkTerminal {
            val c = sumBy { it }
            assertEquals(sourceList.sumBy { it }, c)
        }
    }

    @Test
    fun testSubByDouble() {
        checkTerminal {
            val c = sumByDouble { it.toDouble() }
            assertEquals(sourceList.sumByDouble { it.toDouble() }, c)
        }
    }

    @Test
    fun testPartition() {
        checkTerminal {
            val pair = partition { it % 2 == 0 }
            assertEquals(sourceList.partition { it % 2 == 0 }, pair)
        }
    }

    @Test
    fun testZip() {
        val expect = sourceList.zip(sourceList) { a, b -> a + 2 * b }
        checkTransform(expect) { ctx ->
            zip(testSource(ctx), ctx) { a, b -> a + 2*b }
        }
        checkTransform(expect) { ctx ->
            testSource(ctx).zip(this, ctx) { a, b -> a + 2*b }
        }
    }

    // ------------------
    
    private fun checkTerminal(
        expected: ((Throwable?) -> Unit)? = null,
        terminal: suspend ReceiveChannel<Int>.() -> Unit
    ) {
        checkTerminalCompletion(expected, terminal)
        checkTerminalCancellation(expected, terminal)
    }

    private fun checkTerminalCompletion(
        expected: ((Throwable?) -> Unit)? = null,
        terminal: suspend ReceiveChannel<Int>.() -> Unit
    ) {
        val src = runBlocking {
            val src = testSource(coroutineContext)
            try {
                // terminal operation
                terminal(src)
                // source must be cancelled at the end of terminal op
                if (expected != null) error("Exception was expected")
            } catch (e: Throwable) {
                if (expected == null) throw e
                expected(e)
            }
            src
        }
        assertTrue(src.isClosedForReceive, "Source must be closed")
    }

    private fun checkTerminalCancellation(
        expected: ((Throwable?) -> Unit)? = null,
        terminal: suspend ReceiveChannel<Int>.() -> Unit
    ) {
        val src = runBlocking {
            val src = testSource(coroutineContext)
            // terminal operation in a separate async context started until the first suspension
            val d = async(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
                terminal(src)
            }
            // then cancel it
            d.cancel()
            // and try to get it's result
            try {
                d.await()
            } catch (e: CancellationException) {
                // ok -- was cancelled
            } catch (e: Throwable) {
                // if threw a different exception -- must be an expected one
                if (expected == null) throw e
                expected(e)
            }
            src
        }
        // source must be cancelled at the end of terminal op even if it was cancelled while in process
        assertTrue(src.isClosedForReceive, "Source must be closed")
    }

    private fun <R> checkTransform(
        expect: List<R>,
        transform: ReceiveChannel<Int>.(CoroutineContext) -> ReceiveChannel<R>
    ) {
        // check for varying number of received elements from the channel
        for (nReceive in 0..expect.size) {
            checkTransform(nReceive, expect, transform)
        }
    }

    private fun <R> checkTransform(
        nReceive: Int,
        expect: List<R>,
        transform: ReceiveChannel<Int>.(CoroutineContext) -> ReceiveChannel<R>
    ) {
        val src = runBlocking {
            val src = testSource(coroutineContext)
            // transform
            val res = transform(src, coroutineContext)
            // receive nReceive elements from the result
            repeat(nReceive) { i ->
                assertEquals(expect[i], res.receive())
            }
            if (nReceive < expect.size) {
                // then cancel
                res.cancel()
            } else {
                // then check that result is closed
                assertEquals(null, res.receiveOrNull(), "Result has unexpected values")
            }
            src
        }
        // source must be cancelled when runBlocking processes all the scheduled stuff
        assertTrue(src.isClosedForReceive, "Source must be closed")
    }
}