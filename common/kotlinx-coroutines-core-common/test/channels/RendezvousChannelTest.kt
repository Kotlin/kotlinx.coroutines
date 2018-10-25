/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class RendezvousChannelTest : TestBase() {
    @Test
    fun testSimple() = runTest {
        val q = Channel<Int>(Channel.RENDEZVOUS)
        check(q.isEmpty && q.isFull)
        expect(1)
        val sender = launch {
            expect(4)
            q.send(1) // suspend -- the first to come to rendezvous
            expect(7)
            q.send(2) // does not suspend -- receiver is there
            expect(8)
        }
        expect(2)
        val receiver = launch {
            expect(5)
            check(q.receive() == 1) // does not suspend -- sender was there
            expect(6)
            check(q.receive() == 2) // suspends
            expect(9)
        }
        expect(3)
        sender.join()
        receiver.join()
        check(q.isEmpty && q.isFull)
        finish(10)
    }

    @Test
    fun testClosedReceiveOrNull() = runTest {
        val q = Channel<Int>(Channel.RENDEZVOUS)
        check(q.isEmpty && q.isFull && !q.isClosedForSend && !q.isClosedForReceive)
        expect(1)
        launch {
            expect(3)
            assertEquals(42, q.receiveOrNull())
            expect(4)
            assertEquals(null, q.receiveOrNull())
            expect(6)
        }
        expect(2)
        q.send(42)
        expect(5)
        q.close()
        check(!q.isEmpty && !q.isFull && q.isClosedForSend && q.isClosedForReceive)
        yield()
        check(!q.isEmpty && !q.isFull && q.isClosedForSend && q.isClosedForReceive)
        finish(7)
    }

    @Test
    fun testClosedExceptions() = runTest {
        val q = Channel<Int>(Channel.RENDEZVOUS)
        expect(1)
        launch {
            expect(4)
            try { q.receive() }
            catch (e: ClosedReceiveChannelException) {
                expect(5)
            }
        }
        expect(2)
        q.close()
        expect(3)
        yield()
        expect(6)
        try { q.send(42) }
        catch (e: ClosedSendChannelException) {
            finish(7)
        }
    }

    @Test
    fun testOfferAndPool() = runTest {
        val q = Channel<Int>(Channel.RENDEZVOUS)
        assertFalse(q.offer(1))
        expect(1)
        launch {
            expect(3)
            assertEquals(null, q.poll())
            expect(4)
            assertEquals(2, q.receive())
            expect(7)
            assertEquals(null, q.poll())
            yield()
            expect(9)
            assertEquals(3, q.poll())
            expect(10)
        }
        expect(2)
        yield()
        expect(5)
        assertTrue(q.offer(2))
        expect(6)
        yield()
        expect(8)
        q.send(3)
        finish(11)
    }

    @Test
    fun testIteratorClosed() = runTest {
        val q = Channel<Int>(Channel.RENDEZVOUS)
        expect(1)
        launch {
            expect(3)
            q.close()
            expect(4)
        }
        expect(2)
        for (x in q) {
            expectUnreached()
        }
        finish(5)
    }

    @Test
    fun testIteratorOne() = runTest {
        val q = Channel<Int>(Channel.RENDEZVOUS)
        expect(1)
        launch {
            expect(3)
            q.send(1)
            expect(4)
            q.close()
            expect(5)
        }
        expect(2)
        for (x in q) {
            expect(6)
            assertEquals(1, x)
        }
        finish(7)
    }

    @Test
    fun testIteratorOneWithYield() = runTest {
        val q = Channel<Int>(Channel.RENDEZVOUS)
        expect(1)
        launch {
            expect(3)
            q.send(1) // will suspend
            expect(6)
            q.close()
            expect(7)
        }
        expect(2)
        yield() // yield to sender coroutine right before starting for loop
        expect(4)
        for (x in q) {
            expect(5)
            assertEquals(1, x)
        }
        finish(8)
    }

    @Test
    fun testIteratorTwo() = runTest {
        val q = Channel<Int>(Channel.RENDEZVOUS)
        expect(1)
        launch {
            expect(3)
            q.send(1)
            expect(4)
            q.send(2)
            expect(7)
            q.close()
            expect(8)
        }
        expect(2)
        for (x in q) {
            when (x) {
                1 -> expect(5)
                2 -> expect(6)
                else -> expectUnreached()
            }
        }
        finish(9)
    }

    @Test
    fun testIteratorTwoWithYield() = runTest {
        val q = Channel<Int>(Channel.RENDEZVOUS)
        expect(1)
        launch {
            expect(3)
            q.send(1) // will suspend
            expect(6)
            q.send(2)
            expect(7)
            q.close()
            expect(8)
        }
        expect(2)
        yield() // yield to sender coroutine right before starting for loop
        expect(4)
        for (x in q) {
            when (x) {
                1 -> expect(5)
                2 -> expect(9)
                else -> expectUnreached()
            }
        }
        finish(10)
    }

    @Test
    fun testSuspendSendOnClosedChannel() = runTest {
        val q = Channel<Int>(Channel.RENDEZVOUS)
        expect(1)
        launch {
            expect(4)
            q.send(42) // suspend
            expect(11)
        }
        expect(2)
        launch {
            expect(5)
            q.close()
            expect(6)
        }
        expect(3)
        yield() // to sender
        expect(7)
        yield() // try to resume sender (it will not resume despite the close!)
        expect(8)
        assertEquals(42, q.receiveOrNull())
        expect(9)
        assertNull(q.receiveOrNull())
        expect(10)
        yield() // to sender, it was resumed!
        finish(12)
    }

    class BadClass {
        override fun equals(other: Any?): Boolean = error("equals")
        override fun hashCode(): Int = error("hashCode")
        override fun toString(): String = error("toString")
    }

    @Test
    fun testProduceBadClass() = runTest {
        val bad = BadClass()
        val c = produce {
            expect(1)
            send(bad)
        }
        assertTrue(c.receive() === bad)
        finish(2)
    }

    @Test
    fun testConsumeAll() = runTest {
        val q = Channel<Int>(Channel.RENDEZVOUS)
        for (i in 1..10) {
            launch(start = CoroutineStart.UNDISPATCHED) {
                expect(i)
                q.send(i) // suspends
                expectUnreached() // will get cancelled by cancel
            }
        }
        expect(11)
        q.cancel()
        check(q.isClosedForSend)
        check(q.isClosedForReceive)
        check(q.receiveOrNull() == null)
        finish(12)
    }

    @Test
    fun testCancelWithCause() = runTest({ it is TestException }) {
        val channel = Channel<Int>(Channel.RENDEZVOUS)
        channel.cancel(TestException())
        channel.receiveOrNull()
    }
}
