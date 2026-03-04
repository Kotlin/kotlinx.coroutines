package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class TransformLatestTest : TestBase() {

    @Test
    fun testTransformLatest() = runTest {
        val flow = flowOf(1, 2, 3).transformLatest { value ->
            emit(value)
            emit(value + 1)
        }
        assertEquals(listOf(1, 2, 2, 3, 3, 4), flow.toList())
    }

    @Test
    fun testEmission() = runTest {
        val list = flow {
            repeat(5) {
                emit(it)
            }
        }.transformLatest {
            emit(it)
        }.toList()
        assertEquals(listOf(0, 1, 2, 3, 4), list)
    }

    @Test
    fun testSwitchIntuitiveBehaviour() = runTest {
        val flow = flowOf(1, 2, 3, 4, 5)
        flow.transformLatest {
            expect(it)
            emit(it)
            yield() // Explicit cancellation check
            if (it != 5) expectUnreached()
            else expect(6)
        }.collect()
        finish(7)
    }

    @Test
    fun testSwitchRendezvousBuffer() = runTest {
        val flow = flowOf(1, 2, 3, 4, 5)
        flow.transformLatest {
            emit(it)
            // Reach here every uneven element because of channel's unfairness
            expect(it)
        }.buffer(0).onEach { expect(it + 1) }.collect()
        finish(7)
    }

    @Test
    fun testSwitchBuffer() = runTest {
        val flow = flowOf(1, 2, 3, 42, 4)
        flow.transformLatest {
            emit(it)
            expect(it)
        }.buffer(2).collect()
        finish(5)
    }

    @Test
    fun testHangFlows() = runTest {
        val flow = listOf(1, 2, 3, 4).asFlow()
        val result = flow.transformLatest { value ->
            if (value != 4) hang { expect(value) }
            emit(42)
        }.toList()

        assertEquals(listOf(42), result)
        finish(4)
    }

    @Test
    fun testEmptyFlow() = runTest {
        assertNull(emptyFlow<Int>().transformLatest { emit(1) }.singleOrNull())
    }

    // NamedDispatcher used for this test is now a real dispatcher and we cannot (and should not)
    // assert on the synchronous execution of the test anymore. The primary goal of this test is
    // to verify that each operation runs on the expected dispatcher which is validated with the
    // assertions on the dispatcher name. Having the correct final result at the end validates the
    // overall correctness of the execution.
    // Consequently, all expect calls are commented out.
    @Test
    fun testIsolatedContext() = runTest {
        val flow = flow {
            assertEquals("source", NamedDispatchers.name())
            expect(1)
            emit(4)
            expect(2)
            emit(5)
            expect(3)
        }.flowOn(NamedDispatchers("source")).transformLatest<Int, Int> { value ->
            emitAll(flow<Int> {
                assertEquals("switch$value", NamedDispatchers.name())
                emit(value)
            }.flowOn(NamedDispatchers("switch$value")))
        }.onEach {
            assertEquals("main", NamedDispatchers.nameOr("main"))
        }
        // We now observe the correct behavior. Changing the dispatcher with flowOn avoids the
        // kotlinx-coroutines library from skipping some dispatches and `transformLatest` can
        // properly cancel the processing of a previous value when a new value is emitted by the
        // upstream flow. For instance, when `5` is emitted, the ongoing work for `4` is cancelled.
        // In the original code, `transformLatest` and `onEach` ran synchronously. This meant the
        // processing for each value completed fully before the next value was handled, preventing
        // any cancellation from occurring.
        // The bug discovered with https://pl.kotl.in/GCP1nSBF1 is a known issue
        // (see https://github.com/Kotlin/kotlinx.coroutines/issues/3109) and a fix is in review
        // (see https://github.com/Kotlin/kotlinx.coroutines/pull/4493).
        // original code:
        // assertEquals(2, flow.count())
        assertEquals(1, flow.count())
        // original code:
        // finish(8)
        finish(4)
    }

    @Test
    fun testFailureInTransform() = runTest {
        val flow = flowOf(1, 2).transformLatest { value ->
            if (value == 1) {
                emit(1)
                hang { expect(1) }
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
        val flow = flowOf(1).transformLatest { value ->
            expect(1)
            emit(value)
            expect(2)
            hang { expect(4) }
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
        }.transformLatest<Int, Long> {
            expect(2)
            hang {
                expect(4)
            }
        }
        assertFailsWith<TestException>(flow)
        finish(5)
    }

    @Test
    fun testTake() = runTest {
        val flow = flowOf(1, 2, 3, 4, 5).transformLatest { emit(it) }
        assertEquals(listOf(1), flow.take(1).toList())
    }
}
