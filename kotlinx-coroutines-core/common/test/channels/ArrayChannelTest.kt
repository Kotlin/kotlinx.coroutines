/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class ArrayChannelTest : TestBase() {
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
        finish(10)
    }

    @Test
    fun testClosedBufferedReceiveOrNull() = runTest {
        val q = Channel<Int>(1)
        check(q.isEmpty && !q.isClosedForSend && !q.isClosedForReceive)
        expect(1)
        launch {
            expect(5)
            check(!q.isEmpty && q.isClosedForSend && !q.isClosedForReceive)
            assertEquals(42, q.receiveOrNull())
            expect(6)
            check(!q.isEmpty && q.isClosedForSend && q.isClosedForReceive)
            assertNull(q.receiveOrNull())
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
            finish(7)
        }
    }

    @Test
    fun testOfferAndPoll() = runTest {
        val q = Channel<Int>(1)
        assertTrue(q.offer(1))
        expect(1)
        launch {
            expect(3)
            assertEquals(1, q.poll())
            expect(4)
            assertNull(q.poll())
            expect(5)
            assertEquals(2, q.receive()) // suspends
            expect(9)
            assertEquals(3, q.poll())
            expect(10)
            assertNull(q.poll())
            expect(11)
        }
        expect(2)
        yield()
        expect(6)
        assertTrue(q.offer(2))
        expect(7)
        assertTrue(q.offer(3))
        expect(8)
        assertFalse(q.offer(4))
        yield()
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
        assertFailsWith<CancellationException> { q.receiveOrNull() }
        finish(12)
    }

    @Test
    fun testCancelWithCause() = runTest({ it is TestCancellationException }) {
        val channel = Channel<Int>(5)
        channel.cancel(TestCancellationException())
        channel.receiveOrNull()
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
            channel.offer(-1)
        }
        repeat(4) {
            channel.receiveOrNull()
        }
        checkBufferChannel(channel, capacity)
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
        finish(6)
    }
}
