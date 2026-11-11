package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class FlattenMergeTest : FlatMapMergeBaseTest() {

    override fun <T> Flow<T>.flatMap(mapper: suspend (T) -> Flow<T>): Flow<T> = map(mapper).flattenMerge()

    @Test
    override fun testFlatMapConcurrency() = runTest {
        var concurrentRequests = 0
        val flow = (1..100).asFlow().map { value ->
            flow {
                ++concurrentRequests
                emit(value)
                delay(Long.MAX_VALUE)
            }
        }.flattenMerge(concurrency = 2)

        val consumer = launch {
            flow.collect { value ->
                expect(value)
            }
        }

        repeat(4) {
            yield()
        }

        assertEquals(2, concurrentRequests)
        consumer.cancelAndJoin()
        finish(3)
    }

    @Test
    fun testContextPreservationAcrossFlows() = runTest {
        val result = flow {
            flowOf(1, 2).flatMapMerge {
                flow {
                    yield()
                    emit(it)
                }
            }.collect {
                emit(it)
            }
        }.toList()
        assertEquals(listOf(1, 2), result)
    }

    @Test
    fun testConflatedProduceIn() = runTest {
        val completed = CompletableDeferred<Unit>()
        val source = flow {
            emit(1)
            emit(2)
            emit(3)
            completed.complete(Unit)
        }

        val channel = flowOf(source)
            .flattenMerge(concurrency = 2)
            .conflate()
            .produceIn(this)

        try {
            repeat(100) {
                if (!completed.isCompleted) yield()
            }

            assertTrue(completed.isCompleted)
            assertEquals(3, channel.receive())
        } finally {
            channel.cancel()
        }
    }

    @Test
    fun testDropOldestProduceIn() = runTest {
        val completed = CompletableDeferred<Unit>()
        val source = flow {
            emit(1)
            emit(2)
            emit(3)
            completed.complete(Unit)
        }

        val channel = flowOf(source)
            .flattenMerge(concurrency = 2)
            .buffer(capacity = 0, onBufferOverflow = BufferOverflow.DROP_OLDEST)
            .produceIn(this)

        try {
            repeat(100) {
                if (!completed.isCompleted) yield()
            }

            assertTrue(completed.isCompleted)
            assertEquals(3, channel.receive())
        } finally {
            channel.cancel()
        }
    }

    @Test
    fun testDropLatestProduceIn() = runTest {
        val completed = CompletableDeferred<Unit>()
        val source = flow {
            emit(1)
            emit(2)
            emit(3)
            completed.complete(Unit)
        }

        val channel = flowOf(source)
            .flattenMerge(concurrency = 2)
            .buffer(capacity = 0, onBufferOverflow = BufferOverflow.DROP_LATEST)
            .produceIn(this)

        try {
            repeat(100) {
                if (!completed.isCompleted) yield()
            }

            assertTrue(completed.isCompleted)
            assertEquals(1, channel.receive())
        } finally {
            channel.cancel()
        }
    }
}
