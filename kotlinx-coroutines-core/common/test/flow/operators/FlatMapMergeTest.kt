package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import kotlin.test.*

class FlatMapMergeTest : FlatMapMergeBaseTest() {

    override fun <T> Flow<T>.flatMap(mapper: suspend (T) -> Flow<T>): Flow<T> = flatMapMerge(transform = mapper)

    @Test
    override fun testFlatMapConcurrency() = runTest {
        var concurrentRequests = 0
        val flow = (1..100).asFlow().flatMapMerge(concurrency = 2) { value ->
            flow {
                ++concurrentRequests
                emit(value)
                delay(Long.MAX_VALUE)
            }
        }

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
    fun testAtomicStart() = runTest {
        try {
            coroutineScope {
                val job = coroutineContext[Job]!!
                val flow = flow {
                    expect(3)
                    emit(1)
                }
                    .onCompletion { expect(5) }
                    .flatMapMerge {
                        expect(4)
                        flowOf(it).onCompletion { expectUnreached() } }
                    .onCompletion { expect(6) }

                launch {
                    expect(1)
                    flow.collect()
                }
                launch {
                    expect(2)
                    yield()
                    job.cancel()
                }
            }
        } catch (e: CancellationException) {
            finish(7)
        }
    }

    @Test
    fun testCancellationExceptionDownstream() = runTest {
        val flow = flowOf(1, 2, 3).flatMapMerge {
            flow {
                emit(it)
                throw CancellationException("")
            }
        }

        assertEquals(listOf(1, 2, 3), flow.toList())
    }

    @Test
    fun testCancellationExceptionUpstream() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            yield()
            throw CancellationException("")
        }.flatMapMerge {
            flow {
                expect(3)
                emit(it)
                hang { expect(4) }
            }
        }

        assertFailsWith<CancellationException>(flow)
        finish(5)
    }

    @Test
    fun testCancellation() = runTest {
        val result = flow {
            emit(1)
            emit(2)
            emit(3)
            emit(4)
            expectUnreached() // Cancelled by take
            emit(5)
        }.flatMapMerge(2) { v -> flow { emit(v) } }
            .take(2)
            .toList()
        assertEquals(listOf(1, 2), result)
    }
}
