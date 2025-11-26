package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlin.test.*

/**
 * Properties stay the same regardless of whether the channel was closed with or without exception.
 */
class ChannelPropertiesAfterClosingTest : TestBase() {
    @Test
    fun testClosedIsClosedForReceive() = runTest {
        TestChannelKind.entries.forEach { kind ->
            for (exception in listOf(null, TestException())) {
                val channel = kind.create<Int>()
                assertFalse(channel.isClosedForReceive)
                channel.close(exception)
                assertTrue(channel.isClosedForReceive)
            }
        }
    }

    @Test
    fun testClosedIsEmptyFalse() = runTest {
        TestChannelKind.entries.forEach { kind ->
            for (exception in listOf(null, TestException())) {
                val channel = kind.create<Int>()
                assertTrue(channel.isEmpty)
                assertFalse(channel.isClosedForReceive)
                channel.close(exception)
                // NB! Not obvious.
                assertFalse(channel.isEmpty)
                assertTrue(channel.isClosedForReceive)
            }
        }
    }

    @Test
    fun testSendClosedReceiveIsEmptyFalse() = runTest {
        for (exception in listOf(null, TestException())) {
            val channel = Channel<Int>(1)
            assertTrue(channel.isEmpty)
            assertFalse(channel.isClosedForReceive)
            channel.send(1)
            assertFalse(channel.isEmpty)
            assertFalse(channel.isClosedForReceive)
            channel.close(exception)
            assertFalse(channel.isEmpty)
            assertFalse(channel.isClosedForReceive)
            channel.receive()
            assertFalse(channel.isEmpty)
            assertTrue(channel.isClosedForReceive)
        }
    }
}
