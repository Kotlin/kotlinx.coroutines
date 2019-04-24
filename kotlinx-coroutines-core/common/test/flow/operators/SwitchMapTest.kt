/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class SwitchMapTest : TestBase() {

    @Test
    fun testConstantDynamic() = runTest {
        val flow = flowOf(1, 2, 3).switchMap { value -> (value until value + 3).asFlow() }
        assertEquals(listOf(1, 2, 3, 2, 3, 4, 3, 4, 5), flow.toList())
    }

    @Test
    fun testHangFlows() = runTest {
        val flow = listOf(1, 2, 3, 4).asFlow()
        val result = flow.switchMap { value ->
            flow {
                if (value != 4) hang { expect(value) }
                else emit(42)
            }
        }.toList()

        assertEquals(listOf(42), result)
        finish(4)
    }

    @Test
    fun testEmptyFlow() = runTest {
        assertNull(emptyFlow<Int>().switchMap { flowOf(1) }.singleOrNull())
    }

    @Test
    fun testIsolatedContext() = runTest {
        val flow = flow {
            assertEquals("source", NamedDispatchers.name())
            expect(1)
            emit(2)
            emit(4)
        }.flowOn(NamedDispatchers("source")).switchMap { value ->
            flow {
                assertEquals("switch$value", NamedDispatchers.name())
                emit(value)
                expect(value)
            }.flowOn(NamedDispatchers("switch$value"))
        }.onEach {
            expect(it + 1)
            assertEquals("main", NamedDispatchers.nameOr("main"))
        }

        assertEquals(2, flow.count())
        finish(6)
    }

    @Test
    fun testFailureInTransform() = runTest {
        val flow = flowOf(1, 2).switchMap { value ->
            if (value == 1) {
                flow {
                    emit(1)
                    hang { expect(1) }
                }
            } else {
                expect(2)
                throw TestException()
            }
        }

        assertFailsWith<TestException>(flow)
        finish(3)
    }

    @Test
    fun testFailureDownstream() = runTest {
        val flow = flowOf(1).switchMap { value ->
            flow {
                expect(1)
                emit(value)
                expect(2)
                hang { expect(4) }
            }
        }.flowOn(NamedDispatchers("downstream")).map {
            expect(3)
            throw TestException()
            it
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
        }.switchMap {
            flow<Int> {
                expect(2)
                hang {
                    expect(4)
                }
            }
        }

        assertFailsWith<TestException>(flow)
        finish(5)
    }
}
