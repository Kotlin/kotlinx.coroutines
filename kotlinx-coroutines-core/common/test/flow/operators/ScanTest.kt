/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class ScanTest : TestBase() {
    @Test
    fun testScan() = runTest {
        val flow = flowOf(1, 2, 3, 4, 5)
        val result = flow.scanReduce { acc, v -> acc + v }.toList()
        assertEquals(listOf(1, 3, 6, 10, 15), result)
    }

    @Test
    fun testScanWithInitial() = runTest {
        val flow = flowOf(1, 2, 3)
        val result = flow.scan(emptyList<Int>()) { acc, value -> acc + value }.toList()
        assertEquals(listOf(emptyList(), listOf(1), listOf(1, 2), listOf(1, 2, 3)), result)
    }

    @Test
    fun testNulls() = runTest {
        val flow = flowOf(null, 2, null, null, null, 5)
        val result = flow.scanReduce { acc, v ->  if (v == null) acc else (if (acc == null) v else acc + v) }.toList()
        assertEquals(listOf(null, 2, 2, 2, 2, 7), result)
    }

    @Test
    fun testEmptyFlow() = runTest {
        val result = emptyFlow<Int>().scanReduce { _, _ -> 1 }.toList()
        assertTrue(result.isEmpty())
    }

    @Test
    fun testErrorCancelsUpstream() = runTest {
        expect(1)
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    hang { expect(3) }
                }
                emit(1)
                emit(2)
            }
        }.scanReduce { _, value ->
            expect(value) // 2
            latch.receive()
            throw TestException()
        }.catch { /* ignore */ }

        assertEquals(1, flow.single())
        finish(4)
    }

    public operator fun <T> Collection<T>.plus(element: T): List<T> {
        val result = ArrayList<T>(size + 1)
        result.addAll(this)
        result.add(element)
        return result
    }
}
