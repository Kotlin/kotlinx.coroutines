package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class FoldTest : TestBase() {
    @Test
    fun testFold() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
        }

        val result = flow.fold(3) { value, acc -> value + acc }
        assertEquals(6, result)
    }

    @Test
    fun testEmptyFold() = runTest {
        val flow = flowOf<Int>()
        assertEquals(42, flow.fold(42) { value, acc -> value + acc })
    }

    @Test
    fun testErrorCancelsUpstream() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    expect(3)
                    hang { expect(5) }
                }
                expect(2)
                emit(1)
            }
        }

        expect(1)
        assertFailsWith<TestException> {
            flow.fold(42) { _, _ ->
                latch.receive()
                expect(4)
                throw TestException()
            }
        }
        finish(6)
    }
}
