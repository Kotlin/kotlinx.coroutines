/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

abstract class FlatMapBaseTest : TestBase() {

    abstract fun <T> Flow<T>.flatMap(mapper: suspend (T) -> Flow<T>): Flow<T>

    @Test
    fun testFlatMap() = runTest {
        val n = 100
        val sum = (1..100).asFlow()
            .flatMap { value ->
                // 1 + (1 + 2) + (1 + 2 + 3) + ... (1 + .. + n)
                flow {
                    repeat(value) {
                        emit(it + 1)
                    }
                }
            }.sum()

        assertEquals(n * (n + 1) * (n + 2) / 6, sum)
    }

    @Test
    fun testSingle() = runTest {
        val flow = flow {
            repeat(100) {
                emit(it)
            }
        }.flatMap { value ->
            if (value == 99) flowOf(42)
            else flowOf()
        }

        val value = flow.single()
        assertEquals(42, value)
    }

    @Test
    fun testNulls() = runTest {
        val list = flowOf(1, null, 2).flatMap {
            flowOf(1, null, null, 2)
        }.toList()

        assertEquals(List(3) { listOf(1, null, null, 2)}.flatten(), list)
    }

    @Test
    fun testContext() = runTest {
        val captured = ArrayList<String>()
        val flow = flowOf(1)
            .flowOn(NamedDispatchers("irrelevant"))
            .flatMap {
                captured += NamedDispatchers.name()
                flow {
                    captured += NamedDispatchers.name()
                    emit(it)
                }
            }

        flow.flowOn(NamedDispatchers("1")).sum()
        flow.flowOn(NamedDispatchers("2")).sum()
        assertEquals(listOf("1", "1", "2", "2"), captured)
    }

    @Test
    fun testIsolatedContext() = runTest {
        val flow = flowOf(1)
            .flowOn(NamedDispatchers("irrelevant"))
            .flatMap {
                    flow {
                        assertEquals("inner", NamedDispatchers.name())
                        emit(it)
                    }
            }.flowOn(NamedDispatchers("inner"))
            .flatMap {
                flow {
                    assertEquals("outer", NamedDispatchers.name())
                    emit(it)
                }
            }.flowOn(NamedDispatchers("outer"))

        assertEquals(1, flow.singleOrNull())
    }
}
