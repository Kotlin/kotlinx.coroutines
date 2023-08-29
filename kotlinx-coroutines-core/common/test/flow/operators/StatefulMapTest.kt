/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class StatefulMapTest : TestBase() {

    private fun <T> Flow<T>.zipWithIndex(): Flow<Pair<T, Long>> = statefulMap(0L) { index, value ->
        return@statefulMap Pair(index + 1L, Pair(value, index))
    }

    @Test
    fun testStatefulMap() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
            emit(3)
        }
        assertEquals(listOf(Pair(1, 0L), Pair(2, 1L), Pair(3, 2L)), flow.zipWithIndex().toList())
    }

    @Test
    fun testStatefulMapWithOnCompletion() = runTest {
        val flow = flow {
            emit("a")
            emit("b")
            emit("c")
        }
        val flow2: Flow<Any> = flow.statefulMap(0, { it }) { counter, value ->
            return@statefulMap Pair(counter + 1, value)
        }
        assertEquals(listOf("a", "b", "c", 3), flow2.toList())
    }

    @Test
    fun testEmptyFlow() = runTest {
        val sum = emptyFlow<Int>().statefulMap(1) { state, value ->
            expectUnreached()
            Pair(state, value)
        }.sum()
        assertEquals(0, sum)
    }

    private fun <T> Flow<T>.grouped(size: Int): Flow<List<T>> =
        statefulMap(mutableListOf<T>(), { value -> value.toList() }) { acc, value ->
            if (acc.size < size) {
                acc.add(value)
            }
            if (acc.size == size) {
                val result = acc.toList()
                acc.clear()
                return@statefulMap Pair(acc, result)
            }
            return@statefulMap Pair(acc, emptyList<T>())
        }.filterNot(List<T>::isEmpty)

    @Test
    fun testGrouped() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
            emit(3)
            emit(4)
            emit(5)
        }
        assertEquals(listOf(listOf(1, 2), listOf(3, 4), listOf(5)), flow.grouped(2).toList())
    }

    private fun <T> Flow<T>.distinct(): Flow<T?> = statefulMap(mutableSetOf<T>()) { set, value ->
        if (set.add(value)) {
            return@statefulMap Pair(set, value)
        }
        return@statefulMap Pair(set, null)
    }.filterNotNull()

    @Test
    fun testAsDistinct() = runTest {
        val flow = flow {
            emit(1)
            emit(1)
            emit(2)
            emit(2)
            emit(3)
            emit(3)
        }
        assertEquals(listOf(1, 2, 3), flow.distinct().toList())
    }

    @Test
    fun testErrorCancelsUpstream() = runTest {
        var cancelled = false
        val latch = Channel<Unit>()
        val flow: Flow<Int> = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    hang { cancelled = true }
                }
                emit(1)
                expectUnreached()
            }
        }.statefulMap<Int, Int, Int>(1) { _, _ ->
            latch.receive()
            throw TestException()
        }.catch { emit(42) }

        assertEquals(42, flow.single())
        assertTrue(cancelled)
    }
}
