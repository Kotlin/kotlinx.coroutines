/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class ConflatedChannelTest : TestBase() {
    @Test
    fun testBasicConflationOfferPoll() {
        val q = Channel<Int>(Channel.CONFLATED)
        assertNull(q.poll())
        assertTrue(q.offer(1))
        assertTrue(q.offer(2))
        assertTrue(q.offer(3))
        assertEquals(3, q.poll())
        assertNull(q.poll())
    }

    @Test
    fun testConflatedSend() = runTest {
        val q = ConflatedChannel<Int>()
        q.send(1)
        q.send(2) // shall conflated previously sent
        assertEquals(2, q.receiveOrNull())
    }

    @Test
    fun testConflatedClose() = runTest {
        val q = Channel<Int>(Channel.CONFLATED)
        q.send(1)
        q.close() // shall conflate sent item and become closed
        assertNull(q.receiveOrNull())
    }

    @Test
    fun testConflationSendReceive() = runTest {
        val q = Channel<Int>(Channel.CONFLATED)
        expect(1)
        launch { // receiver coroutine
            expect(4)
            assertEquals(2, q.receive())
            expect(5)
            assertEquals(3, q.receive()) // this receive suspends
            expect(8)
            assertEquals(6, q.receive()) // last conflated value
            expect(9)
        }
        expect(2)
        q.send(1)
        q.send(2) // shall conflate
        expect(3)
        yield() // to receiver
        expect(6)
        q.send(3) // send to the waiting receiver
        q.send(4) // buffer
        q.send(5) // conflate
        q.send(6) // conflate again
        expect(7)
        yield() // to receiver
        finish(10)
    }

    @Test
    fun testConsumeAll() = runTest {
        val q = Channel<Int>(Channel.CONFLATED)
        expect(1)
        for (i in 1..10) {
            q.send(i) // stores as last
        }
        q.cancel()
        check(q.isClosedForSend)
        check(q.isClosedForReceive)
        check(q.receiveOrNull() == null)
        finish(2)
    }

    @Test
    fun testCancelWithCause() = runTest({ it is TestException }) {
        val channel = Channel<Int>(Channel.CONFLATED)
        channel.cancel(TestException())
        channel.receiveOrNull()
    }
}
