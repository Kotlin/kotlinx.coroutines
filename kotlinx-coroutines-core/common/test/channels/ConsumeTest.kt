/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

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
