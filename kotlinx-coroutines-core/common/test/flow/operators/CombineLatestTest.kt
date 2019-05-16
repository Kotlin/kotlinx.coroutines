/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.combineLatest as combineLatestOriginal
import kotlin.test.*

/*
 * Replace:  { i, j -> i + j } ->  { i, j -> i + j } as soon as KT-30991 is fixed
 */
abstract class CombineLatestTestBase : TestBase() {

    abstract fun <T1, T2, R> Flow<T1>.combineLatest(other: Flow<T2>, transform: suspend (T1, T2) -> R): Flow<R>

    @Test
    fun testCombineLatest() = runTest {
        val flow = flowOf("a", "b", "c")
        val flow2 = flowOf(1, 2, 3)
        val list = flow.combineLatest(flow2) { i, j -> i + j }.toList()
        assertEquals(listOf("a1", "b1", "b2", "c2", "c3"), list)
    }

    @Test
    fun testNulls() = runTest {
        val flow = flowOf("a", null, null)
        val flow2 = flowOf(1, 2, 3)
        val list = flow.combineLatest(flow2, { i, j -> i + j }).toList()
        assertEquals(listOf("a1", "null1", "null2", "null2", "null3"), list)
    }

    @Test
    fun testNullsOther() = runTest {
        val flow = flowOf("a", "b", "c")
        val flow2 = flowOf(null, 2, null)
        val list = flow.combineLatest(flow2, { i, j -> i + j }).toList()
        assertEquals(listOf("anull", "bnull", "b2", "c2", "cnull"), list)
    }

    @Test
    fun testEmptyFlow() = runTest {
        val flow = emptyFlow<String>().combineLatest(emptyFlow<Int>(), { i, j -> i + j })
        assertNull(flow.singleOrNull())
    }

    @Test
    fun testFirstIsEmpty() = runTest {
        val f1 = emptyFlow<String>()
        val f2 = flowOf(1)
        assertEquals(emptyList(), f1.combineLatest(f2) { i, j -> i + j }.toList())
    }

    @Test
    fun testSecondIsEmpty() = runTest {
        val f1 = flowOf("a")
        val f2 = emptyFlow<Int>()
        assertEquals(emptyList(), f1.combineLatest(f2) { i, j -> i + j }.toList())
    }

    @Test
    fun testPreservingOrder() = runTest {
        val f1 = flow {
            expect(1)
            emit("a")
            expect(3)
            emit("b")
            emit("c")
            expect(4)
        }

        val f2 = flow {
            expect(2)
            emit(1)
            yield()
            yield()
            expect(5)
            emit(2)
            expect(6)
            yield()
            expect(7)
            emit(3)
        }

        val result = f1.combineLatest(f2) { i, j -> i + j }.toList()
        assertEquals(listOf("a1", "b1", "c1", "c2", "c3"), result)
        finish(8)
    }

    @Test
    fun testPreservingOrderReversed() = runTest {
        val f1 = flow {
            expect(1)
            emit("a")
            expect(3)
            emit("b")
            emit("c")
            expect(4)
        }

        val f2 = flow {
            yield() // One more yield because now this flow starts first
            expect(2)
            emit(1)
            yield()
            yield()
            expect(5)
            emit(2)
            expect(6)
            yield()
            expect(7)
            emit(3)
        }

        val result = f2.combineLatest(f1) { i, j -> j + i }.toList()
        assertEquals(listOf("a1", "b1", "c1", "c2", "c3"), result)
        finish(8)
    }

    @Test
    fun testContextIsIsolated() = runTest {
        val f1 = flow {
            emit("a")
            assertEquals("first", NamedDispatchers.name())
            expect(1)
        }.flowOn(NamedDispatchers("first")).onEach {
            assertEquals("nested", NamedDispatchers.name())
            expect(2)
        }.flowOn(NamedDispatchers("nested"))

        val f2 = flow {
            emit(1)
            assertEquals("second", NamedDispatchers.name())
            expect(3)
        }.flowOn(NamedDispatchers("second")).flowWith(NamedDispatchers("with")) {
            onEach {
                assertEquals("with", NamedDispatchers.name())
                expect(4)
            }
        }

        val value = withContext(NamedDispatchers("main")) {
            f1.combineLatest(f2) { i, j ->
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

        val flow = f1.combineLatest(f2) { i, j ->
            assertEquals("combine", NamedDispatchers.name())
            expect(1)
            i + j
        }.flowOn(NamedDispatchers("combine")).onEach {
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

        val flow = f1.combineLatest(f2) { _, _ -> 1 }
        assertFailsWith<TestException>(flow)
        finish(2)
    }
}

class CombineLatestTest : CombineLatestTestBase() {
    override fun <T1, T2, R> Flow<T1>.combineLatest(other: Flow<T2>, transform: suspend (T1, T2) -> R): Flow<R> = combineLatestOriginal(other, transform)
}

class CombineLatestVarargAdapterTest : CombineLatestTestBase() {
    override fun <T1, T2, R> Flow<T1>.combineLatest(other: Flow<T2>, transform: suspend (T1, T2) -> R): Flow<R> =
        (this as Flow<*>).combineLatestOriginal(other) { args: Array<Any?> -> transform(args[0] as T1, args[1] as T2) }
}