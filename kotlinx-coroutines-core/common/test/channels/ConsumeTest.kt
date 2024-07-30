@file:OptIn(DelicateCoroutinesApi::class)
package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class ConsumeTest: TestBase() {

    /** Check that [ReceiveChannel.consume] does not suffer from KT-58685 */
    @Test
    fun testConsumeJsMiscompilation() = runTest {
        val channel = Channel<Int>()
        assertFailsWith<IndexOutOfBoundsException> {
            try {
                channel.consume { null } ?: throw IndexOutOfBoundsException() // should throw…
            } catch (e: Exception) {
                throw e // …but instead fails here
            }
        }
    }

    /** Checks that [ReceiveChannel.consume] closes the channel when the block executes successfully. */
    @Test
    fun testConsumeClosesOnSuccess() = runTest {
        val channel = Channel<Int>()
        channel.consume { }
        assertTrue(channel.isClosedForReceive)
    }

    /** Checks that [ReceiveChannel.consume] closes the channel when the block executes successfully. */
    @Test
    fun testConsumeClosesOnFailure() = runTest {
        val channel = Channel<Int>()
        try {
            channel.consume { throw TestException() }
        } catch (e: TestException) {
            // Expected
        }
        assertTrue(channel.isClosedForReceive)
    }

    /** Checks that [ReceiveChannel.consume] closes the channel when the block does an early return. */
    @Test
    fun testConsumeClosesOnEarlyReturn() = runTest {
        val channel = Channel<Int>()
        fun f() {
            try {
                channel.consume { return }
            } catch (e: TestException) {
                // Expected
            }
        }
        f()
        assertTrue(channel.isClosedForReceive)
    }

    /** Checks that [ReceiveChannel.consume] closes the channel when the block executes successfully. */
    @Test
    fun testConsumeEachClosesOnSuccess() = runTest {
        val channel = Channel<Int>(Channel.UNLIMITED)
        launch { channel.close() }
        channel.consumeEach { fail("unreached") }
        assertTrue(channel.isClosedForReceive)
    }

    /** Checks that [ReceiveChannel.consume] closes the channel when the block executes successfully. */
    @Test
    fun testConsumeEachClosesOnFailure() = runTest {
        val channel = Channel<Unit>(Channel.UNLIMITED)
        channel.send(Unit)
        try {
            channel.consumeEach { throw TestException() }
        } catch (e: TestException) {
            // Expected
        }
        assertTrue(channel.isClosedForReceive)
    }

    /** Checks that [ReceiveChannel.consume] closes the channel when the block does an early return. */
    @Test
    fun testConsumeEachClosesOnEarlyReturn() = runTest {
        val channel = Channel<Unit>(Channel.UNLIMITED)
        channel.send(Unit)
        suspend fun f() {
            channel.consumeEach {
                return@f
            }
        }
        f()
        assertTrue(channel.isClosedForReceive)
    }

    /** Checks that [ReceiveChannel.consumeEach] reacts to cancellation, but processes the elements that are
     * readily available in the buffer. */
    @Test
    fun testConsumeEachExitsOnCancellation() = runTest {
        val undeliveredElements = mutableListOf<Int>()
        val channel = Channel<Int>(2, onUndeliveredElement = {
            undeliveredElements.add(it)
        })
        launch {
            // These two elements will be sent and put into the buffer:
            channel.send(0)
            channel.send(1)
            // This element will not fit into the buffer, so `send` suspends:
            channel.send(2)
            // At this point, the consumer's `launch` is cancelled.
            yield() // Allow the cancellation handler of the consumer to run.
            // Try to send a new element, which will fail at this point:
            channel.send(3)
            fail("unreached")
        }
        launch {
            channel.consumeEach {
                cancel()
                assertTrue(it in 0..2)
            }
        }.join()
        assertTrue(channel.isClosedForReceive)
        assertEquals(listOf(3), undeliveredElements)
    }

    @Test
    fun testConsumeEachThrowingOnChannelClosing() = runTest {
        val channel = Channel<Int>()
        channel.close(TestException())
        assertFailsWith<TestException> {
            channel.consumeEach { fail("unreached") }
        }
    }

    /** Check that [BroadcastChannel.consume] does not suffer from KT-58685 */
    @Suppress("DEPRECATION", "DEPRECATION_ERROR")
    @Test
    fun testBroadcastChannelConsumeJsMiscompilation() = runTest {
        val channel = BroadcastChannel<Int>(1)
        assertFailsWith<IndexOutOfBoundsException> {
            try {
                channel.consume { null } ?: throw IndexOutOfBoundsException() // should throw…
            } catch (e: Exception) {
                throw e // …but instead fails here
            }
        }
    }
}
