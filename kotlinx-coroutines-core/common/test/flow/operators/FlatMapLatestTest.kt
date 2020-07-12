/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class FlatMapLatestTest : TestBase() {

    @Test
    fun testFlatMapLatest() = runTest {
        val flow = flowOf(1, 2, 3).flatMapLatest { value ->
            flowOf(value, value + 1)
        }
        assertEquals(listOf(1, 2, 2, 3, 3, 4), flow.toList())
    }

    @Test
    fun testEmission() = runTest {
        val list = flow {
            repeat(5) {
                emit(it)
            }
        }.flatMapLatest { flowOf(it) }.toList()
        assertEquals(listOf(0, 1, 2, 3, 4), list)
    }

    @Test
    fun testSwitchIntuitiveBehaviour() = runTest {
        val flow = flowOf(1, 2, 3, 4, 5)
        flow.flatMapLatest {
            flow {
                expect(it)
                emit(it)
                yield() // Explicit cancellation check
                if (it != 5) expectUnreached()
                else expect(6)
            }
        }.collect()
        finish(7)
    }

    @Test
    fun testSwitchRendevouzBuffer() = runTest {
        val flow = flowOf(1, 2, 3, 4, 5)
        flow.flatMapLatest {
            flow {
                emit(it)
                // Reach here every uneven element because of channel's unfairness
                expect(it)
            }
        }.buffer(0).onEach { expect(it + 1) }
            .collect()
        finish(7)
    }

    @Test
    fun testHangFlows() = runTest {
        val flow = listOf(1, 2, 3, 4).asFlow()
        val result = flow.flatMapLatest { value ->
            flow {
                if (value != 4) hang { expect(value) }
                emit(42)
            }
        }.toList()

        assertEquals(listOf(42), result)
        finish(4)
    }

    @Test
    fun testEmptyFlow() = runTest {
        assertNull(emptyFlow<Int>().flatMapLatest { flowOf(1) }.singleOrNull())
    }

    @Test
    fun testFailureInTransform() = runTest {
        val flow = flowOf(1, 2).flatMapLatest { value ->
            flow {
                if (value == 1) {
                    emit(1)
                    hang { expect(1) }
                } else {
                    expect(2)
                    throw TestException()
                }
            }
        }
        assertFailsWith<TestException>(flow)
        finish(3)
    }

    @Test
    fun testFailureDownstream() = runTest {
        val flow = flowOf(1).flatMapLatest { value ->
            flow {
                expect(1)
                emit(value)
                expect(2)
                hang { expect(4) }
            }
        }.flowOn(NamedDispatchers("downstream")).onEach {
            expect(3)
            throw TestException()
        }
        assertFailsWith<TestException>(flow)
        finish(5)
    }

    @Test
    fun testFailureUpstream() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            yield()
            expect(3)
            throw TestException()
        }.flatMapLatest<Int, Long> {
            flow {
                expect(2)
                hang {
                    expect(4)
                }
            }
        }
        assertFailsWith<TestException>(flow)
        finish(5)
    }

    @Test
    fun testTake() = runTest {
        val flow = flowOf(1, 2, 3, 4, 5).flatMapLatest { flowOf(it) }
        assertEquals(listOf(1), flow.take(1).toList())
    }
}
