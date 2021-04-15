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
