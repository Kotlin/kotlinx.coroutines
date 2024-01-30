package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class MapNotNullTest : TestBase() {
    @Test
    fun testMap() = runTest {
        val flow = flow {
            emit(1)
            emit(null)
            emit(2)
        }

        val result = flow.mapNotNull { it }.sum()
        assertEquals(3, result)
    }

    @Test
    fun testEmptyFlow() = runTest {
        val sum = emptyFlow<Int>().mapNotNull { expectUnreached(); it }.sum()
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
            }
        }.mapNotNull<Int, Int> {
            latch.receive()
            throw TestException()
        }.catch { emit(42) }

        assertEquals(42, flow.single())
        assertTrue(cancelled)
    }
}
