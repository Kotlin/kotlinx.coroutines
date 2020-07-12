/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class ChannelBuildersFlowTest : TestBase() {
    @Test
    fun testChannelConsumeAsFlow() = runTest {
        val channel = produce {
           repeat(10) {
               send(it + 1)
           }
        }
        val flow = channel.consumeAsFlow()
        assertEquals(55, flow.sum())
        assertFailsWith<IllegalStateException> { flow.collect() }
    }

    @Test
    fun testChannelReceiveAsFlow() = runTest {
        val channel = produce {
           repeat(10) {
               send(it + 1)
           }
        }
        val flow = channel.receiveAsFlow()
        assertEquals(55, flow.sum())
        assertEquals(emptyList(), flow.toList())
    }

    @Test
    fun testConsumeAsFlowCancellation() = runTest {
        val channel = produce(NonCancellable) { // otherwise failure will cancel scope as well
            repeat(10) {
                send(it + 1)
            }
            throw TestException()
        }
        val flow = channel.consumeAsFlow()
        assertEquals(15, flow.take(5).sum())
        // the channel should have been canceled, even though took only 5 elements
        assertTrue(channel.isClosedForReceive)
        assertFailsWith<IllegalStateException> { flow.collect() }
    }

    @Test
    fun testReceiveAsFlowCancellation() = runTest {
        val channel = produce(NonCancellable) { // otherwise failure will cancel scope as well
            repeat(10) {
                send(it + 1)
            }
            throw TestException()
        }
        val flow = channel.receiveAsFlow()
        assertEquals(15, flow.take(5).sum()) // sum of first 5
        assertEquals(40, flow.take(5).sum()) // sum the rest 5
        assertFailsWith<TestException> { flow.sum() } // exception in the rest
    }

    @Test
    fun testConsumeAsFlowException() = runTest {
        val channel = produce(NonCancellable) { // otherwise failure will cancel scope as well
            repeat(10) {
                send(it + 1)
            }
            throw TestException()
        }
        val flow = channel.consumeAsFlow()
        assertFailsWith<TestException> { flow.sum() }
        assertFailsWith<IllegalStateException> { flow.collect() }
    }

    @Test
    fun testReceiveAsFlowException() = runTest {
        val channel = produce(NonCancellable) { // otherwise failure will cancel scope as well
            repeat(10) {
                send(it + 1)
            }
            throw TestException()
        }
        val flow = channel.receiveAsFlow()
        assertFailsWith<TestException> { flow.sum() }
        assertFailsWith<TestException> { flow.collect() } // repeated collection -- same exception
    }

    @Test
    fun testConsumeAsFlowProduceFusing() = runTest {
        val channel = produce { send("OK") }
        val flow = channel.consumeAsFlow()
        assertSame(channel, flow.produceIn(this))
        assertFailsWith<IllegalStateException> { flow.produceIn(this) }
        channel.cancel()
    }

    @Test
    fun testReceiveAsFlowProduceFusing() = runTest {
        val channel = produce { send("OK") }
        val flow = channel.receiveAsFlow()
        assertSame(channel, flow.produceIn(this))
        assertSame(channel, flow.produceIn(this)) // can use produce multiple times
        channel.cancel()
    }

    @Test
    fun testConsumeAsFlowProduceBuffered() = runTest {
        expect(1)
        val channel = produce {
            expect(3)
            (1..10).forEach { send(it) }
            expect(4) // produces everything because of buffering
        }
        val flow = channel.consumeAsFlow().buffer() // request buffering
        expect(2) // producer is not running yet
        val result = flow.produceIn(this)
        // run the flow pipeline until it consumes everything into buffer
        while (!channel.isClosedForReceive) yield()
        expect(5) // produced had done running (buffered stuff)
        assertNotSame(channel, result)
        assertFailsWith<IllegalStateException> { flow.produceIn(this) }
        // check that we received everything
        assertEquals((1..10).toList(), result.toList())
        finish(6)
    }

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
        expect(1)
        val channel = broadcast(NonCancellable) { // otherwise failure will cancel scope as well
            repeat(10) {
                send(it + 1)
            }
            throw TestException()
        }
        assertEquals(15, channel.asFlow().take(5).sum())

        // Workaround for JS bug
        try {
            channel.asFlow().collect { /* Do nothing */ }
            expectUnreached()
        } catch (e: TestException) {
            finish(2)
        }
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

    @Test
    fun testProduceInAtomicity() = runTest {
        val flow = flowOf(1).onCompletion { expect(2) }
        val scope = CoroutineScope(wrapperDispatcher())
        flow.produceIn(scope)
        expect(1)
        scope.cancel()
        scope.coroutineContext[Job]?.join()
        finish(3)
    }
}
