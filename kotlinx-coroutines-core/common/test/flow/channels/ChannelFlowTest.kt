/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class ChannelFlowTest : TestBase() {
    @Test
    fun testBroadcastChannelAsFlow() = runTest {
        val channel = broadcast {
           repeat(10) {
               send(it + 1)
           }
        }

        val sum = channel.asFlow().sum()
        assertEquals(55, sum)
    }

    @Test
    fun testExceptionInBroadcast() = runTest {
        val channel = broadcast(NonCancellable) { // otherwise failure will cancel scope as well
            repeat(10) {
                send(it + 1)
            }
            throw TestException()
        }
        assertEquals(15, channel.asFlow().take(5).sum())
        assertFailsWith<TestException>(channel.asFlow())
    }

    @Test
    fun testBroadcastChannelAsFlowLimits() = runTest {
        val channel = BroadcastChannel<Int>(1)
        val flow = channel.asFlow().map { it * it }.drop(1).take(2)

        var expected = 0
        launch {
            assertTrue(channel.offer(1)) // Handed to the coroutine
            assertTrue(channel.offer(2)) // Buffered
            assertFalse(channel.offer(3)) // Failed to offer
            channel.send(3)
            yield()
            assertEquals(1, expected)
            assertTrue(channel.offer(4)) // Handed to the coroutine
            assertTrue(channel.offer(5)) // Buffered
            assertFalse(channel.offer(6))  // Failed to offer
            channel.send(6)
            assertEquals(2, expected)
        }

        val sum = flow.sum()
        assertEquals(13, sum)
        ++expected
        val sum2 = flow.sum()
        assertEquals(61, sum2)
        ++expected
    }

    @Test
    fun flowAsBroadcast() = runTest {
        val flow = flow {
            repeat(10) {
                emit(it)
            }
        }

        val channel = flow.broadcastIn(this)
        assertEquals((0..9).toList(), channel.openSubscription().toList())
    }

    @Test
    fun flowAsBroadcastMultipleSubscription() = runTest {
        val flow = flow {
            repeat(10) {
                emit(it)
            }
        }

        val broadcast = flow.broadcastIn(this)
        val channel = broadcast.openSubscription()
        val channel2 = broadcast.openSubscription()

        assertEquals(0, channel.receive())
        assertEquals(0, channel2.receive())
        yield()
        assertEquals(1, channel.receive())
        assertEquals(1, channel2.receive())

        channel.cancel()
        channel2.cancel()
        yield()
        ensureActive()
    }

    @Test
    fun flowAsBroadcastException() = runTest {
        val flow = flow {
            repeat(10) {
                emit(it)
            }

            throw TestException()
        }

        val channel = flow.broadcastIn(this + NonCancellable)
        assertFailsWith<TestException> { channel.openSubscription().toList() }
        assertTrue(channel.isClosedForSend) // Failure in the flow fails the channel
    }

    // Semantics of these tests puzzle me, we should figure out the way to prohibit such chains
    @Test
    fun testFlowAsBroadcastAsFlow() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
            emit(3)
        }.broadcastIn(this).asFlow()

        assertEquals(6, flow.sum())
        assertEquals(0, flow.sum()) // Well suddenly flow is no longer idempotent and cold
    }

    @Test
    fun testBroadcastAsFlowAsBroadcast() = runTest {
        val channel = broadcast {
            send(1)
        }.asFlow().broadcastIn(this)

        channel.openSubscription().consumeEach {
            assertEquals(1, it)
        }

        channel.openSubscription().consumeEach {
            fail()
        }
    }
}
