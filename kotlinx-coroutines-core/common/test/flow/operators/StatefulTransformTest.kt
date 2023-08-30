/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class StatefulTransformTest : TestBase() {

    private suspend fun <T> Flow<T>.zipWithIndex(): Flow<Pair<T, Long>> = statefulTransform {
        var index = 0L;
        { value ->
            emit(Pair(value, index++))
        }
    }

    @Test
    fun testStatefulTransform() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
            emit(3)
        }
        assertEquals(
            listOf(Pair(1, 0L), Pair(2, 1L), Pair(3, 2L)), flow.zipWithIndex().toList()
        )
    }

    @Test
    fun testEmptyFlow() = runTest {
        val sum = emptyFlow<Int>().statefulTransform<Int, Int> {
            var state = 0
            {
                expectUnreached()
                state++
                it
            }
        }.sum()
        assertEquals(0, sum)
    }

    private fun <T> Flow<T>.grouped(size: Int): Flow<List<T>> = statefulTransform {
        val acc = mutableListOf<T>();
        { value ->
            acc.add(value)
            if (acc.size == size) {
                val list = acc.toList()
                acc.clear()
                emit(list)
            }
        }
    }

    @Test
    fun testGrouped() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
            emit(3)
            emit(4)
            emit(5)
        }
        assertEquals(listOf(listOf(1, 2), listOf(3, 4)), flow.grouped(2).toList())
    }

    private fun <T> Flow<T>.distinct(): Flow<T?> = statefulTransform {
        val set = mutableSetOf<T>();
        { value ->
            if (set.add(value)) {
                emit(value);
            }
        }
    }

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
        }.statefulTransform<Int, Int> {

            {
                latch.receive()
                throw TestException()
            }
        }.catch { emit(42) }

        assertEquals(42, flow.single())
        assertTrue(cancelled)
    }
}
