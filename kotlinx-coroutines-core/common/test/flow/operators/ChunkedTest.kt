package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.*
import kotlin.test.Test
import kotlin.test.assertEquals

class ChunkedTest : TestBase() {

    private val flow = flow {
        emit(1)
        emit(2)
        emit(3)
        emit(4)
    }

    @Test
    fun `Chunks correct number of emissions with possible partial window at the end`() = runTest {
        assertEquals(2, flow.chunked(2).count())
        assertEquals(2, flow.chunked(3).count())
        assertEquals(1, flow.chunked(5).count())
    }

    @Test
    fun `Throws IllegalArgumentException for chunk of size less than 1`() {
        assertFailsWith<IllegalArgumentException> { flow.chunked(0) }
        assertFailsWith<IllegalArgumentException> { flow.chunked(-1) }
    }

    @Test
    fun `No emissions with empty flow`() = runTest {
        assertEquals(0, flowOf<Int>().chunked(2).count())
    }

    @Test
    fun testErrorCancelsUpstream() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch(start = CoroutineStart.ATOMIC) {
                    latch.send(Unit)
                    hang { expect(3) }
                }
                emit(1)
                expect(1)
                emit(2)
                expectUnreached()
            }
        }.chunked<Int, Int>(2) { chunk ->
            expect(2) // 2
            latch.receive()
            throw TestException()
        }.catch { emit(42) }

        assertEquals(42, flow.single())
        finish(4)
    }
}