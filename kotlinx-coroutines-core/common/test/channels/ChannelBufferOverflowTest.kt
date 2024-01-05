package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class ChannelBufferOverflowTest : TestBase() {
    @Test
    fun testDropLatest() = runTest {
        val c = Channel<Int>(2, BufferOverflow.DROP_LATEST)
        assertTrue(c.trySend(1).isSuccess)
        assertTrue(c.trySend(2).isSuccess)
        assertTrue(c.trySend(3).isSuccess) // overflows, dropped
        c.send(4) // overflows dropped
        assertEquals(1, c.receive())
        assertTrue(c.trySend(5).isSuccess)
        assertTrue(c.trySend(6).isSuccess) // overflows, dropped
        assertEquals(2, c.receive())
        assertEquals(5, c.receive())
        assertEquals(null, c.tryReceive().getOrNull())
    }

    @Test
    fun testDropOldest() = runTest {
        val c = Channel<Int>(2, BufferOverflow.DROP_OLDEST)
        assertTrue(c.trySend(1).isSuccess)
        assertTrue(c.trySend(2).isSuccess)
        assertTrue(c.trySend(3).isSuccess) // overflows, keeps 2, 3
        c.send(4) // overflows, keeps 3, 4
        assertEquals(3, c.receive())
        assertTrue(c.trySend(5).isSuccess)
        assertTrue(c.trySend(6).isSuccess) // overflows, keeps 5, 6
        assertEquals(5, c.receive())
        assertEquals(6, c.receive())
        assertEquals(null, c.tryReceive().getOrNull())
    }
}
