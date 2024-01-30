package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*


class ChannelFactoryTest : TestBase() {
    @Test
    fun testRendezvousChannel() {
        assertIs<BufferedChannel<*>>(Channel<Int>())
        assertIs<BufferedChannel<*>>(Channel<Int>(0))
    }

    @Test
    fun testUnlimitedChannel() {
        assertIs<BufferedChannel<*>>(Channel<Int>(Channel.UNLIMITED))
        assertIs<BufferedChannel<*>>(Channel<Int>(Channel.UNLIMITED, BufferOverflow.DROP_OLDEST))
        assertIs<BufferedChannel<*>>(Channel<Int>(Channel.UNLIMITED, BufferOverflow.DROP_LATEST))
    }

    @Test
    fun testConflatedChannel() {
        assertIs<ConflatedBufferedChannel<*>>(Channel<Int>(Channel.CONFLATED))
        assertIs<ConflatedBufferedChannel<*>>(Channel<Int>(1, BufferOverflow.DROP_OLDEST))
    }

    @Test
    fun testBufferedChannel() {
        assertIs<BufferedChannel<*>>(Channel<Int>(1))
        assertIs<ConflatedBufferedChannel<*>>(Channel<Int>(1, BufferOverflow.DROP_LATEST))
        assertIs<BufferedChannel<*>>(Channel<Int>(10))
    }

    @Test
    fun testInvalidCapacityNotSupported() {
        assertFailsWith<IllegalArgumentException> { Channel<Int>(-3) }
    }
    
    @Test
    fun testUnsupportedBufferOverflow() {
        assertFailsWith<IllegalArgumentException> { Channel<Int>(Channel.CONFLATED, BufferOverflow.DROP_OLDEST) }
        assertFailsWith<IllegalArgumentException> { Channel<Int>(Channel.CONFLATED, BufferOverflow.DROP_LATEST) }
    }
}
