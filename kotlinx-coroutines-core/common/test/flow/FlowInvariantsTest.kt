/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.coroutines.*
import kotlin.reflect.*
import kotlin.test.*

class FlowInvariantsTest : TestBase() {

    private fun <T> runParametrizedTest(
        expectedException: KClass<out Throwable>? = null,
        testBody: suspend (flowFactory: (suspend FlowCollector<T>.() -> Unit) -> Flow<T>) -> Unit
    ) = runTest {
        val r1 = runCatching { testBody { flow(it) } }.exceptionOrNull()
        check(r1, expectedException)
        reset()

        val r2 = runCatching { testBody { abstractFlow(it) } }.exceptionOrNull()
        check(r2, expectedException)
    }

    private fun <T> abstractFlow(block: suspend FlowCollector<T>.() -> Unit): Flow<T> = object : AbstractFlow<T>() {
        override suspend fun collectSafely(collector: FlowCollector<T>) {
            collector.block()
        }
    }

    private fun check(exception: Throwable?, expectedException: KClass<out Throwable>?) {
        if (expectedException != null && exception == null) fail("Expected $expectedException, but test completed successfully")
        if (expectedException != null && exception != null) assertTrue(expectedException.isInstance(exception))
        if (expectedException == null && exception != null) throw exception
    }

    @Test
    fun testWithContextContract() = runParametrizedTest<Int>(IllegalStateException::class) { flow ->
        flow {
            withContext(NonCancellable) {
                emit(1)
            }
        }.collect {
            expectUnreached()
        }
    }

    @Test
    fun testWithDispatcherContractViolated() = runParametrizedTest<Int>(IllegalStateException::class) { flow ->
        flow {
            withContext(NamedDispatchers("foo")) {
                emit(1)
            }
        }.collect {
            expectUnreached()
        }
    }

    @Test
    fun testWithNameContractViolated() = runParametrizedTest<Int>(IllegalStateException::class) { flow ->
        flow {
            withContext(CoroutineName("foo")) {
                emit(1)
            }
        }.collect {
            expectUnreached()
        }
    }

    @Test
    fun testWithContextDoesNotChangeExecution() = runTest {
        val flow = flow {
            emit(NamedDispatchers.name())
        }.flowOn(NamedDispatchers("original"))

        var result = "unknown"
        withContext(NamedDispatchers("misc")) {
            flow
                .flowOn(NamedDispatchers("upstream"))
                .launchIn(this + NamedDispatchers("consumer")) {
                    onEach {
                        result = it
                    }
                }.join()
        }
        assertEquals("original", result)
    }

    @Test
    fun testScopedJob() = runParametrizedTest<Int>(IllegalStateException::class) { flow ->
        flow { emit(1) }.buffer(EmptyCoroutineContext, flow).collect {
            expect(1)
        }
        finish(2)
    }

    @Test
    fun testScopedJobWithViolation() = runParametrizedTest<Int>(IllegalStateException::class) { flow ->
        flow { emit(1) }.buffer(Dispatchers.Unconfined, flow).collect {
            expect(1)
        }
        finish(2)
    }

    @Test
    fun testMergeViolation() = runParametrizedTest<Int> { flow ->
        fun Flow<Int>.merge(other: Flow<Int>): Flow<Int> = flow {
            coroutineScope {
                launch {
                    collect { value -> emit(value) }
                }
                other.collect { value -> emit(value) }
            }
        }

        fun Flow<Int>.trickyMerge(other: Flow<Int>): Flow<Int> = flow {
            coroutineScope {
                launch {
                    collect { value ->
                        coroutineScope { emit(value) }
                    }
                }
                other.collect { value -> emit(value) }
            }
        }

        val flowInstance = flowOf(1)
        assertFailsWith<IllegalStateException> { flowInstance.merge(flowInstance).toList() }
        assertFailsWith<IllegalStateException> { flowInstance.trickyMerge(flowInstance).toList() }
    }

    @Test
    fun testNoMergeViolation() = runTest {
        fun Flow<Int>.merge(other: Flow<Int>): Flow<Int> = channelFlow {
            launch {
                collect { value -> send(value) }
            }
            other.collect { value -> send(value) }
        }

        fun Flow<Int>.trickyMerge(other: Flow<Int>): Flow<Int> = channelFlow {
            coroutineScope {
                launch {
                    collect { value ->
                        coroutineScope { send(value) }
                    }
                }
                other.collect { value -> send(value) }
            }
        }

        val flow = flowOf(1)
        assertEquals(listOf(1, 1), flow.merge(flow).toList())
        assertEquals(listOf(1, 1), flow.trickyMerge(flow).toList())
    }

    @Test
    fun testScopedCoroutineNoViolation() = runParametrizedTest<Int> { flow ->
        fun Flow<Int>.buffer(): Flow<Int> = flow {
            coroutineScope {
                val channel = produce {
                    collect {
                        send(it)
                    }
                }
                channel.consumeEach {
                    emit(it)
                }
            }
        }
        assertEquals(listOf(1, 1), flowOf(1, 1).buffer().toList())
    }

    private fun Flow<Int>.buffer(coroutineContext: CoroutineContext, flow: (suspend FlowCollector<Int>.() -> Unit) -> Flow<Int>): Flow<Int> = flow {
        coroutineScope {
            val channel = Channel<Int>()
            launch {
                collect { value ->
                    channel.send(value)
                }
                channel.close()
            }

            launch(coroutineContext) {
                for (i in channel) {
                    emit(i)
                }
            }
        }
    }

    @Test
    fun testEmptyCoroutineContext() = runTest {
        emptyContextTest {
            map {
                expect(it)
                it + 1
            }
        }
    }

    @Test
    fun testEmptyCoroutineContextTransform() = runTest {
        emptyContextTest {
            transform {
                expect(it)
                emit(it + 1)
            }
        }
    }

    @Test
    fun testEmptyCoroutineContextViolation() = runTest {
        try {
            emptyContextTest {
                transform {
                    expect(it)
                    withContext(Dispatchers.Unconfined) {
                        emit(it + 1)
                    }
                }
            }
            expectUnreached()
        } catch (e: IllegalStateException) {
            assertTrue(e.message!!.contains("Flow invariant is violated"))
            finish(2)
        }
    }

    private suspend fun emptyContextTest(block: Flow<Int>.() -> Flow<Int>) {
        suspend fun collector(): Int {
            var result: Int = -1
            channelFlow {
                send(1)
            }.block()
                .collect {
                    expect(it)
                    result = it
                }
            return result
        }

        val result = withEmptyContext { collector() }
        assertEquals(2, result)
        finish(3)
    }
}
