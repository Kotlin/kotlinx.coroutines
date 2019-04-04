/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class ConcatenateTest : TestBase() {
    @Test
    fun testConcatenate() = runTest {
        val n = 100
        val sum = (1..n).asFlow()
            .map { value ->
                flow {
                    repeat(value) {
                        emit(it + 1)
                    }
            }
        }.concatenate().sum()
        assertEquals(n * (n + 1) * (n + 2) / 6, sum)
    }

    @Test
    fun testSingle() = runTest {
        val flows = flow {
            repeat(100) {
                if (it == 99) emit(flowOf(42))
                else emit(flowOf())
            }
        }

        val value = flows.concatenate().single()
        assertEquals(42, value)
    }


    @Test
    fun testContext() = runTest {
        val flow = flow {
            emit(flow {
                expect(2)
                assertEquals("first", NamedDispatchers.name())
                emit(1)
            }.flowOn(NamedDispatchers("first")))

            emit(flow {
                expect(3)
                assertEquals("second", NamedDispatchers.name())
                emit(1)
            }.flowOn(NamedDispatchers("second")))
        }.concatenate().flowOn(NamedDispatchers("first"))

        expect(1)
        assertEquals(2, flow.sum())
        finish(4)
    }
}
