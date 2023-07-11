/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.test.*

class ChannelUndeliveredElementTest : TestBase() {
    @Test
    fun testSendSuccessfully() = runTest {
        runAllKindsTest { kind ->
            val channel = kind.create<Resource> { it.cancel() }
            val res = Resource("OK")
            launch {
                channel.send(res)
            }
            val ok = channel.receive()
            assertEquals("OK", ok.value)
            assertFalse(res.isCancelled) // was not cancelled
            channel.close()
            assertFalse(res.isCancelled) // still was not cancelled
        }
    }

    @Test
    fun testRendezvousSendCancelled() = runTest {
        val channel = Channel<Resource> { it.cancel() }
        val res = Resource("OK")
        val sender = launch(start = CoroutineStart.UNDISPATCHED) {
            assertFailsWith<CancellationException> {
                channel.send(res) // suspends & get cancelled
            }
        }
        sender.cancelAndJoin()
        assertTrue(res.isCancelled)
    }

    @Test
    fun testBufferedSendCancelled() = runTest {
        val channel = Channel<Resource>(1) { it.cancel() }
        val resA = Resource("A")
        val resB = Resource("B")
        val sender = launch(start = CoroutineStart.UNDISPATCHED) {
            channel.send(resA) // goes to buffer
            assertFailsWith<CancellationException> {
                channel.send(resB) // suspends & get cancelled
            }
        }
        sender.cancelAndJoin()
        assertFalse(resA.isCancelled) // it is in buffer, not cancelled
        assertTrue(resB.isCancelled) // send was cancelled
        channel.cancel() // now cancel the channel
        assertTrue(resA.isCancelled) // now cancelled in buffer
    }

    @Test
    fun testUnlimitedChannelCancelled() = runTest {
        val channel = Channel<Resource>(Channel.UNLIMITED) { it.cancel() }
        val resA = Resource("A")
        val resB = Resource("B")
        channel.send(resA) // goes to buffer
        channel.send(resB) // goes to buffer
        assertFalse(resA.isCancelled) // it is in buffer, not cancelled
        assertFalse(resB.isCancelled) //  it is in buffer, not cancelled
        channel.cancel() // now cancel the channel
        assertTrue(resA.isCancelled) // now cancelled in buffer
        assertTrue(resB.isCancelled) // now cancelled in buffer
    }

    @Test
    fun testConflatedResourceCancelled() = runTest {
        val channel = Channel<Resource>(Channel.CONFLATED) { it.cancel() }
        val resA = Resource("A")
        val resB = Resource("B")
        channel.send(resA)
        assertFalse(resA.isCancelled)
        assertFalse(resB.isCancelled)
        channel.send(resB)
        assertTrue(resA.isCancelled) // it was conflated (lost) and thus cancelled
        assertFalse(resB.isCancelled)
        channel.close()
        assertFalse(resB.isCancelled) // not cancelled yet, can be still read by receiver
        channel.cancel()
        assertTrue(resB.isCancelled) // now it is cancelled
    }

    @Test
    fun testSendToClosedChannel() = runTest {
        runAllKindsTest { kind ->
            val channel = kind.create<Resource> { it.cancel() }
            channel.close() // immediately close channel
            val res = Resource("OK")
            assertFailsWith<ClosedSendChannelException> {
                channel.send(res) // send fails to closed channel, resource was not delivered
            }
            assertTrue(res.isCancelled)
        }
    }

    private suspend fun runAllKindsTest(test: suspend CoroutineScope.(TestChannelKind) -> Unit) {
        for (kind in TestChannelKind.values()) {
            if (kind.viaBroadcast) continue // does not support onUndeliveredElement
            try {
                withContext(Job()) {
                    test(kind)
                }
            } catch(e: Throwable) {
                error("$kind: $e", e)
            }
        }
    }

    private class Resource(val value: String) {
        private val _cancelled = atomic(false)

        val isCancelled: Boolean
            get() = _cancelled.value

        fun cancel() {
            check(!_cancelled.getAndSet(true)) { "Already cancelled" }
        }
    }

    @Test
    fun testHandlerIsNotInvoked() = runTest { // #2826
        val channel = Channel<Unit> {
            expectUnreached()
        }

        expect(1)
        launch {
            expect(2)
            channel.receive()
        }
        channel.send(Unit)
        finish(3)
    }

    @Test
    fun testChannelBufferOverflow() = runTest {
        testBufferOverflowStrategy(listOf(1, 2), BufferOverflow.DROP_OLDEST)
        testBufferOverflowStrategy(listOf(3), BufferOverflow.DROP_LATEST)
    }

    private suspend fun testBufferOverflowStrategy(expectedDroppedElements: List<Int>, strategy: BufferOverflow) {
        val list = ArrayList<Int>()
        val channel = Channel<Int>(
            capacity = 2,
            onBufferOverflow = strategy,
            onUndeliveredElement = { value -> list.add(value) }
        )

        channel.send(1)
        channel.send(2)

        channel.send(3)
        channel.trySend(4).onFailure { expectUnreached() }
        assertEquals(expectedDroppedElements, list)
    }


    @Test
    fun testTrySendDoesNotInvokeHandlerOnClosedConflatedChannel() = runTest {
        val conflated = Channel<Int>(Channel.CONFLATED, onUndeliveredElement = {
            expectUnreached()
        })
        conflated.close(IndexOutOfBoundsException())
        conflated.trySend(3)
    }

    @Test
    fun testTrySendDoesNotInvokeHandlerOnClosedChannel() = runTest {
        val conflated = Channel<Int>(3, onUndeliveredElement = {
            expectUnreached()
        })
        conflated.close(IndexOutOfBoundsException())
        repeat(10) {
            conflated.trySend(3)
        }
    }

    @Test
    fun testTrySendDoesNotInvokeHandler() {
        for (capacity in 0..2) {
            testTrySendDoesNotInvokeHandler(capacity)
        }
    }

    private fun testTrySendDoesNotInvokeHandler(capacity: Int) {
        val channel = Channel<Int>(capacity, BufferOverflow.DROP_LATEST, onUndeliveredElement = {
            expectUnreached()
        })
        repeat(10) {
            channel.trySend(3)
        }
    }
}
