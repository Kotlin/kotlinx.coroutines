package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlin.test.*

@Suppress("DEPRECATION_ERROR")
class BroadcastChannelFactoryTest : TestBase() {

    @Test
    fun testRendezvousChannelNotSupported() {
        assertFailsWith<IllegalArgumentException> { BroadcastChannel<Int>(0) }
    }

    @Test
    fun testUnlimitedChannelNotSupported() {
        assertFailsWith<IllegalArgumentException> { BroadcastChannel<Int>(Channel.UNLIMITED) }
    }

    @Test
    fun testConflatedBroadcastChannel() {
        assertTrue { BroadcastChannel<Int>(Channel.CONFLATED) is ConflatedBroadcastChannel }
    }

    @Test
    fun testBufferedBroadcastChannel() {
        assertTrue { BroadcastChannel<Int>(1) is BroadcastChannelImpl }
        assertTrue { BroadcastChannel<Int>(10) is BroadcastChannelImpl }
    }

    @Test
    fun testInvalidCapacityNotSupported() {
        assertFailsWith<IllegalArgumentException> { BroadcastChannel<Int>(-3) }
    }
}
