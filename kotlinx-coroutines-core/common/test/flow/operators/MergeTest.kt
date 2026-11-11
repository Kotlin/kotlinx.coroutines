package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*
import kotlinx.coroutines.flow.merge as originalMerge

abstract class MergeTest : TestBase() {

    abstract fun <T> Iterable<Flow<T>>.merge(): Flow<T>

    @Test
    fun testMerge() = runTest {
        val n = 100
        val sum = (1..n).map { flowOf(it) }
            .merge()
            .sum()

        assertEquals(n * (n + 1) / 2, sum)
    }

    @Test
    fun testSingle() = runTest {
        val flow = listOf(flowOf(), flowOf(42), flowOf()).merge()
        val value = flow.single()
        assertEquals(42, value)
    }

    @Test
    fun testNulls() = runTest {
        val list = listOf(flowOf(1), flowOf(null), flowOf(2)).merge().toList()
        assertEquals(listOf(1, null, 2), list)
    }

    @Test
    fun testContext() = runTest {
        val flow = flow {
            emit(NamedDispatchers.name())
        }.flowOn(NamedDispatchers("source"))

        val result = listOf(flow).merge().flowOn(NamedDispatchers("irrelevant")).toList()
        assertEquals(listOf("source"), result)
    }

    @Test
    fun testOneSourceCancelled() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            yield()
            throw CancellationException("")
        }

        val otherFlow = flow {
            repeat(5) {
                emit(1)
                yield()
            }

            expect(3)
        }

        val result = listOf(flow, otherFlow).merge().toList()
        assertEquals(MutableList(6) { 1 }, result)
        finish(4)
    }

    @Test
    fun testOneSourceCancelledNonFused() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            yield()
            throw CancellationException("")
        }

        val otherFlow = flow {
            repeat(5) {
                emit(1)
                yield()
            }

            expect(3)
        }

        val result = listOf(flow, otherFlow).nonFuseableMerge().toList()
        assertEquals(MutableList(6) { 1 }, result)
        finish(4)
    }

    private fun <T> Iterable<Flow<T>>.nonFuseableMerge(): Flow<T> {
        return channelFlow {
            forEach { flow ->
                launch {
                    flow.collect { send(it) }
                }
            }
        }
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

        val channel = listOf(source).merge()
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

        val channel = listOf(source).merge()
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

        val channel = listOf(source).merge()
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

    @Test
    fun testIsolatedContext() = runTest {
        val flow = flow {
            emit(NamedDispatchers.name())
        }

        val result = listOf(flow.flowOn(NamedDispatchers("1")), flow.flowOn(NamedDispatchers("2")))
            .merge()
            .flowOn(NamedDispatchers("irrelevant"))
            .toList()
        assertEquals(listOf("1", "2"), result)
    }
}

class IterableMergeTest : MergeTest() {
    override fun <T> Iterable<Flow<T>>.merge(): Flow<T> = originalMerge()
}

class VarargMergeTest : MergeTest() {
    override fun <T> Iterable<Flow<T>>.merge(): Flow<T> = originalMerge(*toList().toTypedArray())
}
