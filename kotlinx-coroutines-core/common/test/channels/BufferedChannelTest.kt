/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class BufferedChannelTest : TestBase() {
    @Test
    fun testSimple() = runTest {
        val q = Channel<Int>(1)
        check(q.isEmpty)
        expect(1)
        val sender = launch {
            expect(4)
            q.send(1) // success -- buffered
            check(!q.isEmpty)
            expect(5)
            q.send(2) // suspends (buffer full)
            expect(9)
        }
        expect(2)
        val receiver = launch {
            expect(6)
            check(q.receive() == 1) // does not suspend -- took from buffer
            check(!q.isEmpty) // waiting sender's element moved to buffer
            expect(7)
            check(q.receive() == 2) // does not suspend (takes from sender)
            expect(8)
        }
        expect(3)
        sender.join()
        receiver.join()
        check(q.isEmpty)
        (q as BufferedChannel<*>).checkSegmentStructureInvariants()
        finish(10)
    }

    @Test
    fun testClosedBufferedReceiveCatching() = runTest {
        val q = Channel<Int>(1)
        check(q.isEmpty && !q.isClosedForSend && !q.isClosedForReceive)
        expect(1)
        launch {
            expect(5)
            check(!q.isEmpty && q.isClosedForSend && !q.isClosedForReceive)
            assertEquals(42, q.receiveCatching().getOrNull())
            expect(6)
            check(!q.isEmpty && q.isClosedForSend && q.isClosedForReceive)
            assertNull(q.receiveCatching().getOrNull())
            expect(7)
        }
        expect(2)
        q.send(42) // buffers
        expect(3)
        q.close() // goes on
        expect(4)
        check(!q.isEmpty && q.isClosedForSend && !q.isClosedForReceive)
        yield()
        check(!q.isEmpty && q.isClosedForSend && q.isClosedForReceive)
        (q as BufferedChannel<*>).checkSegmentStructureInvariants()
        finish(8)
    }

    @Test
    fun testClosedExceptions() = runTest {
        val q = Channel<Int>(1)
        expect(1)
        launch {
            expect(4)
            try { q.receive() }
            catch (e: ClosedReceiveChannelException) {
                expect(5)
            }
        }
        expect(2)

        require(q.close())
        expect(3)
        yield()
        expect(6)
        try { q.send(42) }
        catch (e: ClosedSendChannelException) {
            (q as BufferedChannel<*>).checkSegmentStructureInvariants()
            finish(7)
        }
    }

    @Test
    fun testTryOp() = runTest {
        val q = Channel<Int>(1)
        assertTrue(q.trySend(1).isSuccess)
        expect(1)
        launch {
            expect(3)
            assertEquals(1, q.tryReceive().getOrNull())
            expect(4)
            assertNull(q.tryReceive().getOrNull())
            expect(5)
            assertEquals(2, q.receive()) // suspends
            expect(9)
            assertEquals(3, q.tryReceive().getOrNull())
            expect(10)
            assertNull(q.tryReceive().getOrNull())
            expect(11)
        }
        expect(2)
        yield()
        expect(6)
        assertTrue(q.trySend(2).isSuccess)
        expect(7)
        assertTrue(q.trySend(3).isSuccess)
        expect(8)
        assertFalse(q.trySend(4).isSuccess)
        yield()
        (q as BufferedChannel<*>).checkSegmentStructureInvariants()
        finish(12)
    }

    @Test
    fun testConsumeAll() = runTest {
        val q = Channel<Int>(5)
        for (i in 1..10) {
            if (i <= 5) {
                expect(i)
                q.send(i) // shall buffer
            } else {
                launch(start = CoroutineStart.UNDISPATCHED) {
                    expect(i)
                    q.send(i) // suspends
                    expectUnreached() // will get cancelled by cancel
                }
            }
        }
        expect(11)
        q.cancel()
        check(q.isClosedForSend)
        check(q.isClosedForReceive)
        assertFailsWith<CancellationException> { q.receiveCatching().getOrThrow() }
        (q as BufferedChannel<*>).checkSegmentStructureInvariants()
        finish(12)
    }

    @Test
    fun testCancelWithCause() = runTest({ it is TestCancellationException }) {
        val channel = Channel<Int>(5)
        channel.cancel(TestCancellationException())
        channel.receive()
    }

    @Test
    fun testBufferSize() = runTest {
        val capacity = 42
        val channel = Channel<Int>(capacity)
        checkBufferChannel(channel, capacity)
    }

    @Test
    fun testBufferSizeFromTheMiddle() = runTest {
        val capacity = 42
        val channel = Channel<Int>(capacity)
        repeat(4) {
            channel.trySend(-1)
        }
        repeat(4) {
            channel.receiveCatching().getOrNull()
        }
        checkBufferChannel(channel, capacity)
    }

    @Test
    fun testBufferIsNotPreallocated() {
        (0..100_000).map { Channel<Int>(Int.MAX_VALUE / 2) }
    }

    private suspend fun CoroutineScope.checkBufferChannel(
        channel: Channel<Int>,
        capacity: Int
    ) {
        launch {
            expect(2)
            repeat(42) {
                channel.send(it)
            }
            expect(3)
            channel.send(42)
            expect(5)
            channel.close()
        }

        expect(1)
        yield()

        expect(4)
        val result = ArrayList<Int>(42)
        channel.consumeEach {
            result.add(it)
        }
        assertEquals((0..capacity).toList(), result)
        (channel as BufferedChannel<*>).checkSegmentStructureInvariants()
        finish(6)
    }
}
