/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class FlowOnTest : TestBase() {

    @Test
    fun testFlowOn() = runTest {
        val source = Source(42)
        val consumer = Consumer(42)

        val flow = source::produce.asFlow()
        flow.flowOn(NamedDispatchers("ctx1")).launchIn(this) {
            onEach { consumer.consume(it) }
        }.join()

        assertEquals("ctx1", source.contextName)
        assertEquals("main", consumer.contextName)

        flow.flowOn(NamedDispatchers("ctx2")).launchIn(this) {
            onEach { consumer.consume(it) }
        }.join()

        assertEquals("ctx2", source.contextName)
        assertEquals("main", consumer.contextName)
    }

    @Test
    fun testFlowOnAndOperators() = runTest {
        val source = Source(42)
        val consumer = Consumer(42)
        val captured = ArrayList<String>()
        val mapper: suspend (Int) -> Int = {
            captured += NamedDispatchers.nameOr("main")
            it
        }

        val flow = source::produce.asFlow()
        flow.map(mapper)
            .flowOn(NamedDispatchers("ctx1"))
            .map(mapper)
            .flowOn(NamedDispatchers("ctx2"))
            .map(mapper)
            .launchIn(this) {
                onEach { consumer.consume(it) }
            }.join()

        assertEquals(listOf("ctx1", "ctx2", "main"), captured)
        assertEquals("ctx1", source.contextName)
        assertEquals("main", consumer.contextName)
    }

    @Test
    public fun testFlowOnThrowingSource() = runTest {
        val flow = flow {
            expect(1)
            emit(NamedDispatchers.name())
            expect(3)
            throw TestException()
        }.map {
            expect(2)
            assertEquals("throwing", it)
            it
        }.flowOn(NamedDispatchers("throwing"))

        assertFailsWith<TestException> { flow.single() }
        ensureActive()
        finish(4)
    }

    @Test
    public fun testFlowOnThrowingOperator() = runTest {
        val flow = flow {
            expect(1)
            emit(NamedDispatchers.name())
            expectUnreached()
        }.map {
            expect(2)
            assertEquals("throwing", it)
            throw TestException()
        }.flowOn(NamedDispatchers("throwing"))

        assertFailsWith<TestException>(flow)
        ensureActive()
        finish(3)
    }

    @Test
    public fun testFlowOnDownstreamOperator() = runTest() {
        val flow = flow {
            expect(2)
            emit(NamedDispatchers.name())
            hang { expect(5) }
            delay(Long.MAX_VALUE)
        }.map {
            expect(3)
            it
        }.flowOn(NamedDispatchers("throwing"))
            .map<String, String> {
                expect(4);
                throw TestException()
            }

        expect(1)
        assertFailsWith<TestException> { flow.single() }
        ensureActive()
        finish(6)
    }

    @Test
    public fun testFlowOnThrowingConsumer() = runTest {
        val flow = flow {
            expect(2)
            emit(NamedDispatchers.name())
            hang { expect(4) }
        }

        expect(1)
        flow.flowOn(NamedDispatchers("...")).launchIn(this + NamedDispatchers("launch")) {
            onEach {
                expect(3)
                throw TestException()
            }
            catch<Throwable> { expect(5) }
        }.join()

        ensureActive()
        finish(6)
    }

    @Test
    fun testFlowOnWithJob() = runTest({ it is IllegalArgumentException }) {
        flow {
            emit(1)
        }.flowOn(NamedDispatchers("foo") + Job())
    }

    @Test
    fun testFlowOnCancellation() = runTest {
        val latch = Channel<Unit>()
        expect(1)
        val job = launch(NamedDispatchers("launch")) {
            flow<Int> {
                expect(2)
                latch.send(Unit)
                expect(3)
                hang {
                    assertEquals("cancelled", NamedDispatchers.name())
                    expect(5)
                }
            }.flowOn(NamedDispatchers("cancelled")).single()
        }

        latch.receive()
        expect(4)
        job.cancel()
        job.join()
        ensureActive()
        finish(6)
    }

    @Test
    fun testFlowOnCancellationHappensBefore() = runTest {
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
                }.flowOn(NamedDispatchers("upstream")).single()
            } catch (e: CancellationException) {
                expect(4)
            }
        }.join()
        ensureActive()
        finish(5)
    }

    @Test
    fun testIndependentOperatorContext() = runTest {
        val value = flow {
            assertEquals("base", NamedDispatchers.nameOr("main"))
            expect(1)
            emit(-239)
        }.map {
            assertEquals("base", NamedDispatchers.nameOr("main"))
            expect(2)
            it
        }.flowOn(NamedDispatchers("base"))
            .map {
                assertEquals("main", NamedDispatchers.nameOr("main"))
                expect(3)
                it
            }.single()

        assertEquals(-239, value)
        finish(4)
    }

    @Test
    fun testMultipleFlowOn() = runTest {
        flow {
            assertEquals("ctx1", NamedDispatchers.nameOr("main"))
            expect(1)
            emit(1)
        }.map {
            assertEquals("ctx1", NamedDispatchers.nameOr("main"))
            expect(2)
        }.flowOn(NamedDispatchers("ctx1"))
            .map {
                assertEquals("ctx2", NamedDispatchers.nameOr("main"))
                expect(3)
            }.flowOn(NamedDispatchers("ctx2"))
            .map {
                assertEquals("ctx3", NamedDispatchers.nameOr("main"))
                expect(4)
            }.flowOn(NamedDispatchers("ctx3"))
            .map {
                assertEquals("main", NamedDispatchers.nameOr("main"))
                expect(5)
            }
            .single()

        finish(6)
    }

    @Test
    fun testTimeoutExceptionUpstream() = runTest {
        val flow = flow {
            emit(1)
            yield()
            withTimeout(-1) {}
            emit(42)
        }.flowOn(NamedDispatchers("foo")).onEach {
            expect(1)
        }
        assertFailsWith<TimeoutCancellationException>(flow)
        finish(2)
    }

    @Test
    fun testTimeoutExceptionDownstream() = runTest {
        val flow = flow {
            emit(1)
            hang { expect(2) }
        }.flowOn(NamedDispatchers("foo")).onEach {
            expect(1)
            withTimeout(-1) {}
        }
        assertFailsWith<TimeoutCancellationException>(flow)
        finish(3)
    }

    @Test
    fun testCancellation() = runTest {
        val result = flow {
            emit(1)
            emit(2)
            emit(3)
            expectUnreached()
            emit(4)
        }.flowOn(wrapperDispatcher())
            .buffer(0)
            .take(2)
            .toList()
        assertEquals(listOf(1, 2), result)
    }

    @Test
    fun testAtomicStart() = runTest {
        try {
            coroutineScope {
                val job = coroutineContext[Job]!!
                val flow = flow {
                    expect(3)
                    emit(1)
                }
                    .onCompletion { expect(4) }
                    .flowOn(wrapperDispatcher())
                    .onCompletion { expect(5) }

                launch {
                    expect(1)
                    flow.collect()
                }
                launch {
                    expect(2)
                    job.cancel()
                }
            }
        } catch (e: CancellationException) {
            finish(6)
        }
    }

    @Test
    fun testException() = runTest {
        val flow = flow {
            emit(314)
            delay(Long.MAX_VALUE)
        }.flowOn(NamedDispatchers("upstream"))
            .map {
                throw TestException()
            }

        assertFailsWith<TestException> { flow.single() }
        assertFailsWith<TestException>(flow)
        ensureActive()
    }

    @Test
    fun testIllegalArgumentException() {
        val flow = emptyFlow<Int>()
        assertFailsWith<IllegalArgumentException> { flow.flowOn(Job()) }
    }

    private inner class Source(private val value: Int) {
        public var contextName: String = "unknown"

        fun produce(): Int {
            contextName = NamedDispatchers.nameOr("main")
            return value
        }
    }

    private inner class Consumer(private val expected: Int) {
        public var contextName: String = "unknown"

        fun consume(value: Int) {
            contextName = NamedDispatchers.nameOr("main")
            assertEquals(expected, value)
        }
    }

    @Test
    fun testCancelledFlowOn() = runTest {
        assertFailsWith<CancellationException> {
            coroutineScope {
                val scope = this
                flow {
                    emit(Unit) // emit to buffer
                    scope.cancel() // now cancel outer scope
                }.flowOn(wrapperDispatcher()).collect {
                    // should not be reached, because cancelled before it runs
                    expectUnreached()
                }
            }
        }
    }
}
