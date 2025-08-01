package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class TransformLatestTest : TestBase() {

    @Test
    fun testTransformLatestSuspension() = runTest {
        val flow = flowOfYielding(1, 2, 3).transformLatest { value ->
            emit(value)
            emit(value + 1)
        }
        assertEquals(listOf(1, 2, 2, 3, 3, 4), flow.toList())
    }

    @Test
    fun testEmission() = runTest {
        val list = flow {
            repeat(5) {
                yield()
                emit(it)
            }
        }.transformLatest {
            emit(it)
        }.toList()
        assertEquals(listOf(0, 1, 2, 3, 4), list)
    }

    @Test
    fun testSwitchIntuitiveBehaviour() = runTest {
        val flow = flowOfYielding(1, 2, 3, 4, 5)
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
        val flow = flowOfYielding(1, 2, 3, 4, 5)
        flow.transformLatest {
            emit(it)
            // Reach here every uneven element because of channel's unfairness
            expect(it)
        }.buffer(0).collect {
            expect(it + 1)
            yield() // give the `flowOfYielding` a chance to cancel the previous flow
        }
        finish(7)
    }

    @Test
    fun testSwitchBuffer() = runTest {
        val allowCollecting = CompletableDeferred<Unit>()
        val flow = flow<Int> {
            emit(-1)
            repeat(10) {
                yield()
                emit(it)
            }
            allowCollecting.complete(Unit)
        }
        flow.transformLatest {
            emit(it)
        }.buffer(2).collect {
            when(it) {
                -1 -> {
                    // a start signal. Now we emulate a slow collector.
                    allowCollecting.await() // sleep for a long time
                }
                0 -> expect(1)
                1 -> expect(2)
                9 -> expect(3)
            }
        }
        finish(4)
    }

    @Test
    fun testHangFlows() = runTest {
        val flow = listOf(1, 2, 3, 4).asFlow().onEach { yield() }
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

    @Test
    fun testIsolatedContext() = runTest {
        val flow = flow {
            assertEquals("source", NamedDispatchers.name())
            expect(1)
            emit(-1) // will be cancelled by the later value
            expect(2)
            emit(4)
            expect(3)
        }.flowOn(NamedDispatchers("source")).transformLatest { value ->
            emitAll(flow<Int> {
                assertEquals("switch$value", NamedDispatchers.name())
                expect(value)
                emit(value)
            }.flowOn(NamedDispatchers("switch$value")))
        }.onEach {
            expect(it + 1)
            assertEquals("main", NamedDispatchers.nameOr("main"))
        }
        assertEquals(1, flow.count())
        finish(6)
    }

    @Test
    fun testFailureInTransform() = runTest {
        val flow = flowOfYielding(1, 2).transformLatest { value ->
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
        val flow = flowOfYielding(1, 2, 3, 4, 5).transformLatest { emit(it) }
        assertEquals(listOf(1), flow.take(1).toList())
    }
}

/**
 * The same as [flowOf] but yields before each emission.
 *
 * This is useful for testing the behavior of operators that cancel the previous emission
 * when a new value is emitted, such as [transformLatest].
 */
internal fun flowOfYielding(vararg values: Int): Flow<Int> = flow {
    for (value in values) {
        yield()
        emit(value)
    }
}
