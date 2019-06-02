/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

/*
 * Replace:  { i, j -> i + j } -> ::sum as soon as KT-30991 is fixed
 */
class ZipTest : TestBase() {

    @Test
    fun testZip() = runTest {
        val f1 = flowOf("a", "b", "c")
        val f2 = flowOf(1, 2, 3)
        assertEquals(listOf("a1", "b2", "c3"), f1.zip(f2,  { i, j -> i + j }).toList())
    }

    @Test
    fun testUnevenZip() = runTest {
        val f1 = flowOf("a", "b", "c", "d", "e")
        val f2 = flowOf(1, 2, 3)
        assertEquals(listOf("a1", "b2", "c3"), f1.zip(f2, { i, j -> i + j }).toList())
        assertEquals(listOf("a1", "b2", "c3"), f2.zip(f1) { i, j -> j + i }.toList())
    }

    @Test
    fun testEmptyFlows() = runTest {
        val f1 = emptyFlow<String>()
        val f2 = emptyFlow<Int>()
        assertEquals(emptyList(), f1.zip(f2,  { i, j -> i + j }).toList())
    }

    @Test
    fun testEmpty() = runTest {
        val f1 = emptyFlow<String>()
        val f2 = flowOf(1)
        assertEquals(emptyList(), f1.zip(f2,  { i, j -> i + j }).toList())
    }

    @Test
    fun testEmptyOther() = runTest {
        val f1 = flowOf("a")
        val f2 = emptyFlow<Int>()
        assertEquals(emptyList(), f1.zip(f2,  { i, j -> i + j }).toList())
    }

    @Test
    fun testNulls() = runTest {
        val f1 = flowOf("a", null, null, "d")
        val f2 = flowOf(1, 2, 3)
        assertEquals(listOf("a1", "null2", "null3"), f1.zip(f2,  { i, j -> i + j }).toList())
    }

    @Test
    fun testNullsOther() = runTest {
        val f1 = flowOf("a", "b", "c")
        val f2 = flowOf(1, null, null, 2)
        assertEquals(listOf("a1", "bnull", "cnull"), f1.zip(f2,  { i, j -> i + j }).toList())
    }

    @Test
    fun testCancelWhenFlowIsDone() = runTest {
        val f1 = flow<String> {
            emit("1")
            emit("2")
            hang {
                expect(1)
            }
        }

        val f2 = flowOf("a", "b")
        assertEquals(listOf("1a", "2b"), f1.zip(f2) { s1, s2 -> s1 + s2 }.toList())
        finish(2)
    }

    @Test
    fun testCancelWhenFlowIsDoneReversed() = runTest {
        val f1 = flow<String> {
            emit("1")
            emit("2")
            hang {
                expect(1)
            }
        }

        val f2 = flowOf("a", "b")
        assertEquals(listOf("a1", "b2"), f2.zip(f1) { s1, s2 -> s1 + s2 }.toList())
        finish(2)
    }

    @Test
    fun testCancesWhenFlowIsDone2() = runTest {
        val f1 = flow<String> {
            emit("1")
            emit("2")
            try {
                emit("3")
                expectUnreached()
            } finally {
                expect(1)
            }

        }

        val f2 = flowOf("a", "b")
        assertEquals(listOf("1a", "2b"), f1.zip(f2) { s1, s2 -> s1 + s2 }.toList())
        finish(2)
    }

    @Test
    fun testContextIsIsolatedReversed() = runTest {
        val f1 = flow {
            emit("a")
            assertEquals("first", NamedDispatchers.name())
            expect(1)
        }.flowOn(NamedDispatchers("first")).onEach {
            assertEquals("with", NamedDispatchers.name())
            expect(2)
        }.flowOn(NamedDispatchers("with"))

        val f2 = flow {
            emit(1)
            assertEquals("second", NamedDispatchers.name())
            expect(3)
        }.flowOn(NamedDispatchers("second")).onEach {
            assertEquals("nested", NamedDispatchers.name())
            expect(4)
        }.flowOn(NamedDispatchers("nested"))

        val value = withContext(NamedDispatchers("main")) {
            f1.zip(f2) { i, j ->
                assertEquals("main", NamedDispatchers.name())
                expect(5)
                i + j
            }.single()
        }

        assertEquals("a1", value)
        finish(6)
    }

    @Test
    fun testErrorInDownstreamCancelsUpstream() = runTest {
        val f1 = flow {
            emit("a")
            hang {
                expect(2)
            }
        }.flowOn(NamedDispatchers("first"))

        val f2 = flow {
            emit(1)
            hang {
                expect(3)
            }
        }.flowOn(NamedDispatchers("second"))

        val flow = f1.zip(f2) { i, j ->
            assertEquals("zip", NamedDispatchers.name())
            expect(1)
            i + j
        }.flowOn(NamedDispatchers("zip")).onEach {
            throw TestException()
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testErrorCancelsSibling() = runTest {
        val f1 = flow {
            emit("a")
            hang {
                expect(1)
            }
        }.flowOn(NamedDispatchers("first"))

        val f2 = flow {
            emit(1)
            throw TestException()
        }.flowOn(NamedDispatchers("second"))

        val flow = f1.zip(f2) { _, _ -> 1 }
        assertFailsWith<TestException>(flow)
        finish(2)
    }
}
