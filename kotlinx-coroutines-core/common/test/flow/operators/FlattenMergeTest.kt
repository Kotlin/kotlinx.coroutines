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
    fun testOverridingBuffer() = runTest {
        for ((capacity, onBufferOverflow, expected) in listOf(
            Triple(1, BufferOverflow.DROP_OLDEST, listOf(0, 20)),
            Triple(1, BufferOverflow.DROP_LATEST, listOf(0, 1)),
            Triple(5, BufferOverflow.DROP_OLDEST, listOf(0, 16, 17, 18, 19, 20)),
            Triple(5, BufferOverflow.DROP_LATEST, listOf(0, 1, 2, 3, 4, 5)),
            Triple(5, BufferOverflow.SUSPEND, (0..20).toList()),
        )) {
            val actual = (0..20).asFlow()
                .flatMapMerge { flowOf(it) }
                .buffer(capacity = capacity, onBufferOverflow = onBufferOverflow)
                .onEach { repeat(20) { yield() } }
                .toList()
            assertEquals(expected, actual)
        }
    }

}
