/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

@Suppress("DEPRECATION")
class FlowWithTest : TestBase() {

    private fun mapper(name: String, index: Int): suspend (Int) -> Int = {
        assertEquals(name, NamedDispatchers.nameOr("main"))
        expect(index)
        it
    }

    @Test
    fun testFlowWith() = runTest {
        val flow = flow {
            assertEquals("main", NamedDispatchers.nameOr("main"))
            expect(1)
            emit(314)
        }

        val result = flow.flowWith(NamedDispatchers("ctx1")) {
            map(mapper("ctx1", 2))
        }.flowWith(NamedDispatchers("ctx2")) {
            map(mapper("ctx2", 3))
        }.map(mapper("main", 4)).single()
        assertEquals(314, result)
        finish(5)
    }

    @Test
    public fun testFlowWithThrowingSource() = runTest {
        val flow = flow {
            emit(NamedDispatchers.nameOr("main"))
            throw TestException()
        }.flowWith(NamedDispatchers("throwing")) {
            map {
                assertEquals("main", it)
                it
            }
        }

        assertFailsWith<TestException> { flow.single() }
        assertFailsWith<TestException>(flow)
        ensureActive()
    }

    @Test
    public fun testFlowWithThrowingOperator() = runTest {
        val flow = flow {
            emit(NamedDispatchers.nameOr("main"))
            hang {}
        }.flowWith(NamedDispatchers("throwing")) {
            map {
                assertEquals("main", it)
                throw TestException()
            }
        }

        assertFailsWith<TestException> { flow.single() }
        assertFailsWith<TestException>(flow)
        ensureActive()
    }

    @Test
    public fun testFlowWithThrowingDownstreamOperator() = runTest {
        val flow = flow {
            emit(42)
            hang {}
        }.flowWith(NamedDispatchers("throwing")) {
            map { it }
        }.map { throw TestException() }

        assertFailsWith<TestException> { flow.single() }
        assertFailsWith<TestException>(flow)
        ensureActive()
    }

    @Test
    fun testMultipleFlowWith() = runTest() {
        flow {
            expect(1)
            emit(1)
        }.map(mapper("main", 2))
            .flowWith(NamedDispatchers("downstream")) {
                map(mapper("downstream", 3))
            }
            .flowWith(NamedDispatchers("downstream 2")) {
                map(mapper("downstream 2", 4))
            }
            .flowWith(NamedDispatchers("downstream 3")) {
                map(mapper("downstream 3", 5))
            }
            .map(mapper("main", 6))
            .flowWith(NamedDispatchers("downstream 4")) {
                map(mapper("downstream 4", 7))
            }.flowWith(NamedDispatchers("ignored")) { this }
            .single()

        finish(8)
    }

    @Test
    fun testFlowWithCancellation() = runTest() {
        val latch = Channel<Unit>()
        expect(1)
        val job = launch(NamedDispatchers("launch")) {
            flow<Int> {
                expect(2)
                latch.send(Unit)
                expect(3)
                hang {
                    assertEquals("launch", NamedDispatchers.nameOr("main"))
                    expect(5)
                }
            }.flowWith(NamedDispatchers("cancelled")) {
                map {
                    expectUnreached()
                    it
                }
            }.single()
        }

        latch.receive()
        expect(4)
        job.cancel()
        job.join()
        ensureActive()
        finish(6)
    }

    @Test
    fun testFlowWithCancellationHappensBefore() = runTest {
        launch {
            try {
                flow<Int> {
                    expect(1)
                    val flowJob = kotlin.coroutines.coroutineContext[Job]!!
                    launch {
                        expect(2)
                        flowJob.cancel()
                    }
                    hang { expect(3) }
                }.flowWith(NamedDispatchers("downstream")) {
                    map { it }
                }.single()
            } catch (e: CancellationException) {
                expect(4)
            }
        }.join()
        finish(5)
    }

    @Test
    fun testMultipleFlowWithException() = runTest() {
        var switch = 0
        val flow = flow {
            emit(Unit)
            if (switch == 0) throw TestException()
        }.map { if (switch == 1) throw TestException() else Unit }
            .flowWith(NamedDispatchers("downstream")) {
                map { if (switch == 2) throw TestException() else Unit }
            }
        repeat(3) {
            switch = it
            assertFailsWith<TestException> { flow.single() }
            assertFailsWith<TestException>(flow)
        }
    }

    @Test
    fun testMultipleFlowWithJobsCancellation() = runTest() {
        val latch = Channel<Unit>()
        val flow = flow {
            expect(1)
            emit(Unit)
            latch.send(Unit)
            hang { expect(4) }
        }.flowWith(NamedDispatchers("downstream")) {
            map {
                expect(2)
                Unit
            }
        }

        val job = launch {
            flow.single()
        }

        latch.receive()
        expect(3)
        job.cancelAndJoin()
        ensureActive()
        finish(5)
    }

    @Test
    fun testTimeoutException() = runTest {
        val flow = flow {
            emit(1)
            yield()
            withTimeout(-1) {}
            emit(42)
        }.flowWith(NamedDispatchers("foo")) {
            onEach { expect(1) }
        }
        assertFailsWith<TimeoutCancellationException>(flow)
        finish(2)
    }

    @Test
    fun testTimeoutExceptionDownstream() = runTest {
        val flow = flow {
            emit(1)
            hang { expect(2) }
        }.flowWith(NamedDispatchers("foo")) {
            onEach {
                expect(1)
                withTimeout(-1) {}
            }
        }
        assertFailsWith<TimeoutCancellationException>(flow)
        finish(3)
    }
}
