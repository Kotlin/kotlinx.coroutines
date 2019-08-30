/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class OnCompletionTest : TestBase() {

    @Test
    fun testOnCompletion() = runTest {
        flow {
            expect(1)
            emit(2)
            expect(4)
        }.onEach {
            expect(2)
        }.onCompletion {
            assertNull(it)
            expect(5)
        }.onEach {
            expect(3)
        }.collect()
        finish(6)
    }

    @Test
    fun testOnCompletionWithException() = runTest {
        flowOf(1).onEach {
            expect(1)
            throw TestException()
        }.onCompletion {
            assertTrue(it is TestException)
            expect(2)
        }.catch {
            assertTrue(it is TestException)
            expect(3)
        }.collect()
        finish(4)
    }

    @Test
    fun testOnCompletionWithExceptionDownstream() = runTest {
        flow {
            expect(1)
            emit(2)
        }.onEach {
            expect(2)
        }.onCompletion {
            assertNull(it)
            expect(4)
        }.onEach {
            expect(3)
            throw TestException()
        }.catch {
            assertTrue(it is TestException)
            expect(5)
        }.collect()
        finish(6)
    }

    @Test
    fun testMultipleOnCompletions() = runTest {
        flowOf(1).onCompletion {
            assertNull(it)
            expect(2)
        }.onEach {
            expect(1)
            throw TestException()
        }.onCompletion {
            assertTrue(it is TestException)
            expect(3)
        }.catch {
            assertTrue(it is TestException)
            expect(4)
        }.collect()
        finish(5)
    }

    @Test
    fun testExceptionFromOnCompletion() = runTest {
        flowOf(1).onEach {
            expect(1)
            throw TestException()
        }.onCompletion {
            expect(2)
            throw TestException2()
        }.catch {
            assertTrue(it is TestException2)
            expect(3)
        }.collect()
        finish(4)
    }

    @Test
    fun testContextPreservation() = runTest {
        flowOf(1).onCompletion {
            assertEquals("OK", NamedDispatchers.name())
            assertNull(it)
            expect(1)
        }.flowOn(NamedDispatchers("OK"))
            .onEach {
                expect(2)
                assertEquals("default", NamedDispatchers.nameOr("default"))
                throw TestException()
            }
            .catch {
                assertTrue(it is TestException)
                expect(3)
            }.collect()
        finish(4)
    }

    @Test
    fun testEmitExample() = runTest {
        val flow = flowOf("a", "b", "c")
            .onCompletion() { emit("Done") }
        assertEquals(listOf("a", "b", "c", "Done"), flow.toList())
    }

    sealed class TestData {
        data class Value(val i: Int) : TestData()
        data class Done(val e: Throwable?) : TestData() {
            override fun equals(other: Any?): Boolean =
                other is Done && other.e?.message == e?.message
        }
    }

    @Test
    fun testCrashedEmit() = runTest {
        expect(1)
        val collected = ArrayList<TestData>()
        assertFailsWith<TestException> {
            (1..10).asFlow()
                .map<Int, TestData> { TestData.Value(it) }
                .onEach { value ->
                    value as TestData.Value
                    expect(value.i + 1)
                    if (value.i == 6) throw TestException("OK")
                    yield()
                }
                .onCompletion { e ->
                    expect(8)
                    assertTrue(e is TestException)
                    emit(TestData.Done(e))
                }.collect {
                    collected += it
                }
        }
        val expected = (1..5).map { TestData.Value(it) } + TestData.Done(TestException("OK"))
        assertEquals(expected, collected)
        finish(9)
    }

    @Test
    fun testCancelledEmit() = runTest {
        expect(1)
        val collected = ArrayList<TestData>()
        assertFailsWith<JobCancellationException> {
            coroutineScope {
                (1..10).asFlow()
                    .map<Int, TestData> { TestData.Value(it) }
                    .onEach { value ->
                        value as TestData.Value
                        expect(value.i + 1)
                        if (value.i == 6) coroutineContext.cancel()
                        yield()
                    }
                    .onCompletion { e ->
                        expect(8)
                        assertNull(e)
                        emit(TestData.Done(e))
                    }.collect {
                        collected += it
                    }
            }
        }
        val expected = (1..5).map { TestData.Value(it) } + TestData.Done(null)
        assertEquals(expected, collected)
        finish(9)
    }
}
