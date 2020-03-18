/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class ReduceTest : TestBase() {
    @Test
    fun testReduce() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
        }

        val result = flow.reduce { value, acc -> value + acc }
        assertEquals(3, result)
    }

    @Test
    fun testEmptyReduce() = runTest {
        val flow = emptyFlow<Int>()
        assertFailsWith<NoSuchElementException> { flow.reduce { acc, value -> value + acc } }
    }

    @Test
    fun testNullableReduce() = runTest {
        val flow = flowOf(1, null, null, 2)
        var invocations = 0
        val sum = flow.reduce { acc, value ->
            ++invocations
            value
        }
        assertEquals(2, sum)
        assertEquals(3, invocations)
    }

    @Test
    fun testReduceNulls() = runTest {
        assertNull(flowOf(null).reduce { _, value -> value })
        assertNull(flowOf(null, null).reduce { _, value -> value })
        assertFailsWith<NoSuchElementException> { flowOf<Nothing?>().reduce { _, value -> value } }
    }

    @Test
    fun testErrorCancelsUpstream() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    expect(3)
                    hang { expect(5) }
                }
                expect(2)
                emit(1)
                emit(2)
            }
        }

        expect(1)
        assertFailsWith<TestException> {
            flow.reduce { _, _ ->
                latch.receive()
                expect(4)
                throw TestException()
                42 // Workaround for KT-30642, return type should not be Nothing
            }
        }
        finish(6)
    }
}
