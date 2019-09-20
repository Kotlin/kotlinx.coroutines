package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.*
import kotlin.test.Test
import kotlin.test.assertEquals

class WindowedTest : TestBase() {

    private val flow = flow {
        emit(1)
        emit(2)
        emit(3)
        emit(4)
    }

    @Test
    fun `Throws IllegalArgumentException for window of size or step less than 1`() {
        assertFailsWith<IllegalArgumentException> { flow.windowed(0, 1, false) }
        assertFailsWith<IllegalArgumentException> { flow.windowed(-1, 2, false) }
        assertFailsWith<IllegalArgumentException> { flow.windowed(2, 0, false) }
        assertFailsWith<IllegalArgumentException> { flow.windowed(5, -2, false) }
    }

    @Test
    fun `No emissions with empty flow`() = runTest {
        assertEquals(0, flowOf<Int>().windowed(2, 2, false).count())
    }

    @Test
    fun `Emits correct sum with overlapping non partial windows`() = runTest {
        assertEquals(15, flow.windowed(3, 1, false) { window ->
            window.sum()
        }.sum())
    }

    @Test
    fun `Emits correct sum with overlapping partial windows`() = runTest {
        assertEquals(13, flow.windowed(3, 2, true) { window ->
            window.sum()
        }.sum())
    }

    @Test
    fun `Emits correct number of overlapping windows for long sequence of overlapping partial windows`() = runTest {
        val elements = generateSequence(1) { it + 1 }.take(100)
        val flow = elements.asFlow().windowed(100, 1, true) { }
        assertEquals(100, flow.count())
    }

    @Test
    fun `Emits correct sum with partial windows set apart`() = runTest {
        assertEquals(7, flow.windowed(2, 3, true) { window ->
            window.sum()
        }.sum())
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
        }.windowed<Int, Int>(2, 3, false) { window ->
            expect(2) // 2
            latch.receive()
            throw TestException()
        }.catch { emit(42) }

        assertEquals(42, flow.single())
        finish(4)
    }
}