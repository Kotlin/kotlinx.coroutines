/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.coroutines.*
import kotlin.test.*

class FlowInvariantsTest : TestBase() {

    @Test
    fun testWithContextContract() = runTest({ it is IllegalStateException }) {
        flow {
            kotlinx.coroutines.withContext(NonCancellable) {
                emit(1)
            }
        }.collect {
            assertEquals(1, it)
        }
    }

    @Test
    fun testWithDispatcherContractViolated() = runTest({ it is IllegalStateException }) {
        flow {
            kotlinx.coroutines.withContext(NamedDispatchers("foo")) {
                emit(1)
            }
        }.collect {
            fail()
        }
    }

    @Test
    fun testCachedInvariantCheckResult() = runTest {
        flow {
            emit(1)

            try {
                kotlinx.coroutines.withContext(NamedDispatchers("foo")) {
                    emit(1)
                }
                fail()
            } catch (e: IllegalStateException) {
                expect(2)
            }

            emit(3)
        }.collect {
            expect(it)
        }
        finish(4)
    }

    @Test
    fun testWithNameContractViolated() = runTest({ it is IllegalStateException }) {
        flow {
            kotlinx.coroutines.withContext(CoroutineName("foo")) {
                emit(1)
            }
        }.collect {
            fail()
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
    fun testScopedJob() = runTest({ it is IllegalStateException }) {
        flow { emit(1) }.buffer(EmptyCoroutineContext).collect {
            expect(1)
        }

        finish(2)
    }

    @Test
    fun testScopedJobWithViolation() = runTest({ it is IllegalStateException }) {
        flow { emit(1) }.buffer(Dispatchers.Unconfined).collect {
            expect(1)
        }

        finish(2)
    }

    @Test
    fun testMergeViolation() = runTest {
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

        val flow = flowOf(1)
        assertFailsWith<IllegalStateException> { flow.merge(flow).toList() }
        assertFailsWith<IllegalStateException> { flow.trickyMerge(flow).toList() }
    }

    // TODO merge artifact
    private fun <T> channelFlow(bufferSize: Int = 16, @BuilderInference block: suspend ProducerScope<T>.() -> Unit): Flow<T> =
        flow {
            coroutineScope {
                val channel = produce(capacity = bufferSize, block = block)
                channel.consumeEach { value ->
                    emit(value)
                }
            }
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
    fun testScopedCoroutineNoViolation() = runTest {
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

    private fun Flow<Int>.buffer(coroutineContext: CoroutineContext): Flow<Int> = flow {
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
}
