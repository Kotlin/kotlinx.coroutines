package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class MapTest : TestBase() {
    @Test
    fun testMap() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
        }

        val result = flow.map { it + 1 }.sum()
        assertEquals(5, result)
    }

    @Test
    fun testEmptyFlow() = runTest {
        val sum = emptyFlow<Int>().map { expectUnreached(); it }.sum()
        assertEquals(0, sum)
    }

    @Test
    fun testErrorCancelsUpstream() = runTest {
        var cancelled = false
        val latch = Channel<Unit>()
        val flow = flow {
            coroutineScope {
                launch {
                    latch.send(Unit)
                    hang { cancelled = true }
                }
                emit(1)
                expectUnreached()
            }
        }.map<Int, Int> {
            latch.receive()
            throw TestException()
        }.catch { emit(42) }

        assertEquals(42, flow.single())
        assertTrue(cancelled)
    }
}
