/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class ArrayBroadcastChannelTest : TestBase() {

    @Test
    fun testConcurrentModification() = runTest {
        val channel = BroadcastChannel<Int>(1)
        val s1 = channel.openSubscription()
        val s2 = channel.openSubscription()

        val job1 = launch(Dispatchers.Unconfined, CoroutineStart.UNDISPATCHED) {
            expect(1)
            s1.receive()
            s1.cancel()
        }

        val job2 = launch(Dispatchers.Unconfined, CoroutineStart.UNDISPATCHED) {
            expect(2)
            s2.receive()
        }

        expect(3)
        channel.send(1)
        joinAll(job1, job2)
        finish(4)
    }

    @Test
    fun testBasic() = runTest {
        expect(1)
        val broadcast = BroadcastChannel<Int>(1)
        assertFalse(broadcast.isClosedForSend)
        val first = broadcast.openSubscription()
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            assertEquals(1, first.receive()) // suspends
            assertFalse(first.isClosedForReceive)
            expect(5)
            assertEquals(2, first.receive()) // suspends
            assertFalse(first.isClosedForReceive)
            expect(10)
            assertNull(first.receiveOrNull()) // suspends
            assertTrue(first.isClosedForReceive)
            expect(14)
        }
        expect(3)
        broadcast.send(1)
        expect(4)
        yield() // to the first receiver
        expect(6)

        val second = broadcast.openSubscription()
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(7)
            assertEquals(2, second.receive()) // suspends
            assertFalse(second.isClosedForReceive)
            expect(11)
            assertNull(second.receiveOrNull()) // suspends
            assertTrue(second.isClosedForReceive)
            expect(15)
        }
        expect(8)
        broadcast.send(2)
        expect(9)
        yield() // to first & second receivers
        expect(12)
        broadcast.close()
        expect(13)
        assertTrue(broadcast.isClosedForSend)
        yield() // to first & second receivers
        finish(16)
    }

    @Test
    fun testSendSuspend() = runTest {
        expect(1)
        val broadcast = BroadcastChannel<Int>(1)
        val first = broadcast.openSubscription()
        launch {
            expect(4)
            assertEquals(1, first.receive())
            expect(5)
            assertEquals(2, first.receive())
            expect(6)
        }
        expect(2)
        broadcast.send(1) // puts to buffer, receiver not running yet
        expect(3)
        broadcast.send(2) // suspends
        finish(7)
    }

    @Test
    fun testConcurrentSendCompletion() = runTest {
        expect(1)
        val broadcast = BroadcastChannel<Int>(1)
        val sub = broadcast.openSubscription()
        // launch 3 concurrent senders (one goes buffer, two other suspend)
        for (x in 1..3) {
            launch(start = CoroutineStart.UNDISPATCHED) {
                expect(x + 1)
                broadcast.send(x)
            }
        }
        // and close it for send
        expect(5)
        broadcast.close()
        // now must receive all 3 items
        expect(6)
        assertFalse(sub.isClosedForReceive)
        for (x in 1..3)
            assertEquals(x, sub.receiveOrNull())
        // and receive close signal
        assertNull(sub.receiveOrNull())
        assertTrue(sub.isClosedForReceive)
        finish(7)
    }

    @Test
    fun testForgetUnsubscribed() = runTest {
        expect(1)
        val broadcast = BroadcastChannel<Int>(1)
        broadcast.send(1)
        broadcast.send(2)
        broadcast.send(3)
        expect(2) // should not suspend anywhere above
        val sub = broadcast.openSubscription()
        launch(start = CoroutineStart.UNDISPATCHED) {
            expect(3)
            assertEquals(4, sub.receive()) // suspends
            expect(5)
        }
        expect(4)
        broadcast.send(4) // sends
        yield()
        finish(6)
    }

    @Test
    fun testReceiveFullAfterClose() = runTest {
        val channel = BroadcastChannel<Int>(10)
        val sub = channel.openSubscription()
        // generate into buffer & close
        for (x in 1..5) channel.send(x)
        channel.close()
        // make sure all of them are consumed
        check(!sub.isClosedForReceive)
        for (x in 1..5) check(sub.receive() == x)
        check(sub.receiveOrNull() == null)
        check(sub.isClosedForReceive)
    }

    @Test
    fun testCloseSubDuringIteration() = runTest {
        val channel = BroadcastChannel<Int>(1)
        // launch generator (for later) in this context
        launch {
            for (x in 1..5) {
                channel.send(x)
            }
            channel.close()
        }
        // start consuming
        val sub = channel.openSubscription()
        var expected = 0
        assertFailsWith<CancellationException> {
            sub.consumeEach {
                check(it == ++expected)
                if (it == 2) {
                    sub.cancel()
                }
            }
        }
        check(expected == 2)
    }

    @Test
    fun testReceiveFromCancelledSub() = runTest {
        val channel = BroadcastChannel<Int>(1)
        val sub = channel.openSubscription()
        assertFalse(sub.isClosedForReceive)
        sub.cancel()
        assertTrue(sub.isClosedForReceive)
        assertFailsWith<CancellationException> { sub.receive() }
    }

    @Test
    fun testCancelWithCause() = runTest({ it is TestCancellationException }) {
        val channel = BroadcastChannel<Int>(1)
        val subscription = channel.openSubscription()
        subscription.cancel(TestCancellationException())
        subscription.receiveOrNull()
    }

    @Test
    fun testReceiveNoneAfterCancel() = runTest {
        val channel = BroadcastChannel<Int>(10)
        val sub = channel.openSubscription()
        // generate into buffer & cancel
        for (x in 1..5) channel.send(x)
        channel.cancel()
        assertTrue(channel.isClosedForSend)
        assertTrue(sub.isClosedForReceive)
        check(sub.receiveOrNull() == null)
    }
}
