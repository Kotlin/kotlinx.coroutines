package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
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
            assertIs<TestException>(it)
            expect(2)
        }.catch {
            assertIs<TestException>(it)
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
            assertIs<TestException>(it) // flow fails because of this exception
            expect(4)
        }.onEach {
            expect(3)
            throw TestException()
        }.catch {
            assertIs<TestException>(it)
            expect(5)
        }.collect()
        finish(6)
    }

    @Test
    fun testMultipleOnCompletions() = runTest {
        flowOf(1).onCompletion {
            assertIs<TestException>(it)
            expect(2)
        }.onEach {
            expect(1)
            throw TestException()
        }.onCompletion {
            assertIs<TestException>(it)
            expect(3)
        }.catch {
            assertIs<TestException>(it)
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
            assertIs<TestException2>(it)
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
                assertIs<TestException>(it)
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
                    assertIs<TestException>(e)
                    emit(TestData.Done(e)) // will fail
                }.collect {
                    collected += it
                }
        }
        val expected: List<TestData> = (1..5).map { TestData.Value(it) }
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
                        assertIs<CancellationException>(e)
                        try {
                            emit(TestData.Done(e))
                            expectUnreached()
                        } finally {
                            expect(9)
                        }
                    }.collect {
                        collected += it
                    }
            }
        }
        val expected = (1..5).map<Int, TestData> { TestData.Value(it) }
        assertEquals(expected, collected)
        finish(10)
    }

    @Test
    fun testFailedEmit() = runTest {
        val cause = TestException()
        assertFailsWith<TestException> {
            flow<TestData> {
                expect(1)
                emit(TestData.Value(2))
                expectUnreached()
            }.onCompletion {
                assertSame(cause, it) // flow failed because of the exception in downstream
                expect(3)
                try {
                    emit(TestData.Done(it))
                    expectUnreached()
                } catch (e: TestException) {
                    assertSame(cause, e)
                    finish(4)
                }
            }.collect {
                expect((it as TestData.Value).i)
                throw cause
            }
        }
    }

    @Test
    fun testFirst() = runTest {
        val value = flowOf(239).onCompletion {
            assertNotNull(it) // the flow did not complete normally
            expect(1)
            try {
                emit(42)
                expectUnreached()
            } catch (e: Throwable) {
                assertTrue { e is AbortFlowException }
            }
        }.first()
        assertEquals(239, value)
        finish(2)
    }

    @Test
    fun testSingle() = runTest {
        assertFailsWith<IllegalArgumentException> {
            flowOf(239).onCompletion {
                assertNull(it)
                expect(1)
                try {
                    emit(42)
                    expectUnreached()
                } catch (e: Throwable) {
                    // Second emit -- failure
                    assertTrue { e is IllegalArgumentException }
                    throw e
                }
            }.single()
            expectUnreached()
        }
        finish(2)
    }

    @Test
    fun testEmptySingleInterference() = runTest {
        val value = emptyFlow<Int>().onCompletion {
            assertNull(it)
            expect(1)
            emit(42)
        }.single()
        assertEquals(42, value)
        finish(2)
    }

    @Test
    fun testTransparencyViolation() = runTest {
        val flow = emptyFlow<Int>().onCompletion {
            expect(2)
            coroutineScope {
                launch {
                    try {
                        emit(1)
                    } catch (e: IllegalStateException) {
                        expect(3)
                    }
                }
            }
        }
        expect(1)
        assertNull(flow.singleOrNull())
        finish(4)
    }

    @Test
    fun testTakeOnCompletion() = runTest {
        // even though it uses "take" from the outside it completes normally
        val flow = (1..10).asFlow().take(5)
        val result = flow.onCompletion { cause ->
            assertNull(cause)
            emit(-1)
        }.toList()
        val expected = (1..5).toList() + (-1)
        assertEquals(expected, result)
    }

    @Test
    fun testCancelledEmitAllFlow() = runTest {
        // emitAll does not call 'collect' on onCompletion collector
        // if the target flow is empty
        flowOf(1, 2, 3)
            .onCompletion { emitAll(MutableSharedFlow()) }
            .take(1)
            .collect()
    }

    @Test
    fun testCancelledEmitAllChannel() = runTest {
        // emitAll does not call 'collect' on onCompletion collector
        // if the target channel is empty
        flowOf(1, 2, 3)
            .onCompletion { emitAll(Channel()) }
            .take(1)
            .collect()
    }

    /**
     * Tests that the operators that are used to limit the flow (like [take] and [zip]) faithfully propagate the
     * cancellation exception to the original owner.
     */
    @Test
    fun testOnCompletionBetweenLimitingOperators() = runTest {
        // `zip` doesn't eat the exception thrown by `take`:
        flowOf(1, 2, 3)
            .zip(flowOf(4, 5)) { a, b -> a + b }
            .onCompletion {
                expect(2)
                assertNotNull(it)
            }
            .take(1)
            .collect {
                expect(1)
            }

        // `take` doesn't eat the exception thrown by `zip`:
        flowOf(1, 2, 3)
            .take(2)
            .onCompletion {
                expect(4)
                assertNotNull(it)
            }
            .zip(flowOf(4)) { a, b -> a + b }
            .collect {
                expect(3)
            }

        // `take` doesn't eat the exception thrown by `first`:
        flowOf(1, 2, 3)
            .take(2)
            .onCompletion {
                expect(5)
                assertNotNull(it)
            }
            .first()

        // `zip` doesn't eat the exception thrown by `first`:
        flowOf(1, 2, 3)
            .zip(flowOf(4, 5)) { a, b -> a + b }
            .onCompletion {
                expect(6)
                assertNotNull(it)
            }
            .first()

        // `take` doesn't eat the exception thrown by another `take`:
        flowOf(1, 2, 3)
            .take(2)
            .onCompletion {
                expect(8)
                assertNotNull(it)
            }
            .take(1)
            .collect {
                expect(7)
            }

        // `zip` doesn't eat the exception thrown by another `zip`:
        flowOf(1, 2, 3)
            .zip(flowOf(4, 5)) { a, b -> a + b }
            .onCompletion {
                expect(10)
                assertNotNull(it)
            }
            .zip(flowOf(6)) { a, b -> a + b }
            .collect {
                expect(9)
            }

        finish(11)
    }

    /**
     * Tests that emitting new elements after completion doesn't overwrite the old elements.
     */
    @Test
    fun testEmittingElementsAfterCancellation() = runTest {
        assertEquals(1, flowOf(1, 2, 3)
            .take(100)
            .onCompletion { emit(4) }
            .first())
    }
}
