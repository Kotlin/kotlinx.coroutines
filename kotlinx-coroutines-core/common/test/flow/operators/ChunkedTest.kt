package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.testing.*
import kotlin.test.*

@OptIn(ExperimentalCoroutinesApi::class)
class ChunkedTest : TestBase() {

    @Test
    fun testChunked() = runTest {
        doTest(flowOf(1, 2, 3, 4, 5), 2, listOf(listOf(1, 2), listOf(3, 4), listOf(5)))
        doTest(flowOf(1, 2, 3, 4, 5), 3, listOf(listOf(1, 2, 3), listOf(4, 5)))
        doTest(flowOf(1, 2, 3, 4), 2, listOf(listOf(1, 2), listOf(3, 4)))
        doTest(flowOf(1), 3, listOf(listOf(1)))
    }

    private suspend fun <T> doTest(flow: Flow<T>, chunkSize: Int, expected: List<List<T>>) {
        assertEquals(expected, flow.chunked(chunkSize).toList())
        assertEquals(flow.toList().chunked(chunkSize), flow.chunked(chunkSize).toList())
    }

    @Test
    fun testEmpty() = runTest {
        doTest(emptyFlow<Int>(), 1, emptyList())
        doTest(emptyFlow<Int>(), 2, emptyList())
    }

    @Test
    fun testChunkedCancelled() = runTest {
        val result = flow {
            expect(1)
            emit(1)
            emit(2)
            expect(2)
        }.chunked(1).buffer().take(1).toList()
        assertEquals(listOf(listOf(1)), result)
        finish(3)
    }

    @Test
    fun testChunkedCancelledWithSuspension() = runTest {
        val result = flow {
            expect(1)
            emit(1)
            yield()
            expectUnreached()
            emit(2)
        }.chunked(1).buffer().take(1).toList()
        assertEquals(listOf(listOf(1)), result)
        finish(2)
    }

    @Test
    fun testChunkedDoesNotIgnoreCancellation() = runTest {
        expect(1)
        val result = flow {
            coroutineScope {
                launch {
                    hang { expect(2) }
                }
                yield()
                emit(1)
                emit(2)
            }
        }.chunked(1).take(1).toList()
        assertEquals(listOf(listOf(1)), result)
        finish(3)
    }

    @Test
    fun testIae() {
        assertFailsWith<IllegalArgumentException> { emptyFlow<Int>().chunked(-1) }
        assertFailsWith<IllegalArgumentException> { emptyFlow<Int>().chunked(0) }
        assertFailsWith<IllegalArgumentException> { emptyFlow<Int>().chunked(Int.MIN_VALUE) }
        assertFailsWith<IllegalArgumentException> { emptyFlow<Int>().chunked(Int.MIN_VALUE + 1) }
    }

    @Test
    fun testSample() = runTest {
        val result = flowOf("a", "b", "c", "d", "e")
            .chunked(2)
            .map { it.joinToString(separator = "") }
            .toList()
        assertEquals(listOf("ab", "cd", "e"), result)
    }
}
