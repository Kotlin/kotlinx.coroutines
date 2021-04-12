/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

open class ConflatedChannelTest : TestBase() {
    protected open fun <T> createConflatedChannel() =
        Channel<T>(Channel.CONFLATED)
    
    @Test
    fun testBasicConflationOfferPoll() {
        val q = createConflatedChannel<Int>()
        assertNull(q.poll())
        assertTrue(q.trySend(1).isSuccess)
        assertTrue(q.trySend(2).isSuccess)
        assertTrue(q.trySend(3).isSuccess)
        assertEquals(3, q.poll())
        assertNull(q.poll())
    }

    @Test
    fun testConflatedSend() = runTest {
        val q = createConflatedChannel<Int>()
        q.send(1)
        q.send(2) // shall conflated previously sent
        assertEquals(2, q.receiveCatching().getOrNull())
    }

    @Test
    fun testConflatedClose() = runTest {
        val q = createConflatedChannel<Int>()
        q.send(1)
        q.close() // shall become closed but do not conflate last sent item yet
        assertTrue(q.isClosedForSend)
        assertFalse(q.isClosedForReceive)
        assertEquals(1, q.receive())
        // not it is closed for receive, too
        assertTrue(q.isClosedForSend)
        assertTrue(q.isClosedForReceive)
        assertNull(q.receiveCatching().getOrNull())
    }

    @Test
    fun testConflationSendReceive() = runTest {
        val q = createConflatedChannel<Int>()
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
        val q = createConflatedChannel<Int>()
        expect(1)
        for (i in 1..10) {
            q.send(i) // stores as last
        }
        q.cancel()
        check(q.isClosedForSend)
        check(q.isClosedForReceive)
        assertFailsWith<CancellationException> { q.receiveCatching().getOrThrow() }
        finish(2)
    }

    @Test
    fun testCancelWithCause() = runTest({ it is TestCancellationException }) {
        val channel = createConflatedChannel<Int>()
        channel.cancel(TestCancellationException())
        channel.receive()
    }
}
