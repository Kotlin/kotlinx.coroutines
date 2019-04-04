/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class ConcatenateMapTest : TestBase() {
    @Test
    fun testConcatenate() = runTest {
        val n = 100
        val sum = flow {
            repeat(n) {
                emit(it + 1) // 1..100
            }
        }.concatenate { value ->
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
        }.concatenate { value ->
            if (value == 99) flowOf(42)
            else flowOf()
        }

        val value = flow.single()
        assertEquals(42, value)
    }

    @Test
    fun testFailure() = runTest {
        var finally = false
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    hang { finally = true }
                }

                emit(1)
            }
        }.concatenate {
            flow<Int> {
                latch.receive()
                throw TestException()
            }
        }

        assertFailsWith<TestException> { flow.count() }
        assertTrue(finally)
    }

    @Test
    fun testFailureInMapOperation() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    hang { expect(3) }
                }

                expect(1)
                emit(1)
            }
        }.concatenate<Int, Int> {
            latch.receive()
            expect(2)
            throw TestException()
            flowOf<Int>() // Workaround for KT-30642, return type should not be Nothing
        }

        assertFailsWith<TestException> { flow.count() }
        finish(4)
    }

    @Test
    fun testContext() = runTest {
        val captured = ArrayList<String>()
        val flow = flowOf(1)
            .flowOn(NamedDispatchers("irrelevant"))
            .concatenate {
                flow {
                    captured += NamedDispatchers.name()
                    emit(it)
                }
            }

        flow.flowOn(NamedDispatchers("1")).sum()
        flow.flowOn(NamedDispatchers("2")).sum()
        assertEquals(listOf("1", "2"), captured)
    }


    @Test
    fun testIsolatedContext() = runTest {
        val flow = flowOf(1)
            .flowOn(NamedDispatchers("irrelevant"))
            .flowWith(NamedDispatchers("inner")) {
                concatenate {
                    flow {
                        expect(2)
                        assertEquals("inner", NamedDispatchers.name())
                        emit(it)
                    }
                }
            }.flowOn(NamedDispatchers("irrelevant"))
            .concatenate {
                flow {
                    expect(3)
                    assertEquals("outer", NamedDispatchers.name())
                    emit(it)
                }
            }.flowOn(NamedDispatchers("outer"))

        expect(1)
        assertEquals(1, flow.single())
        finish(4)
    }
}
