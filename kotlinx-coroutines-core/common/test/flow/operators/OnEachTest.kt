package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class OnEachTest : TestBase() {
    @Test
    fun testOnEach() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
        }

        val result = flow.onEach { expect(it) }.sum()
        assertEquals(3, result)
        finish(3)
    }

    @Test
    fun testEmptyFlow() = runTest {
        val value = emptyFlow<Int>().onEach { fail() }.singleOrNull()
        assertNull(value)
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
        }.onEach {
            latch.receive()
            throw TestException()
        }.catch { emit(42) }

        assertEquals(42, flow.single())
        assertTrue(cancelled)
    }
}
