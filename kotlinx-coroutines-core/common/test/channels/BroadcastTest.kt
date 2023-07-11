/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED")

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import kotlin.test.*

class BroadcastTest : TestBase() {
    @Test
    fun testBroadcastBasic() = runTest {
        expect(1)
        val b = broadcast {
            expect(4)
            send(1) // goes to receiver
            expect(5)
            select<Unit> { onSend(2) {} } // goes to buffer
            expect(6)
            send(3) // suspends, will not be consumes, but will not be cancelled either
            expect(10)
        }
        yield() // has no effect, because default is lazy
        expect(2)
        b.consume {
            expect(3)
            assertEquals(1, receive()) // suspends
            expect(7)
            assertEquals(2, receive()) // suspends
            expect(8)
        }
        expect(9)
        yield() // to broadcast
        finish(11)
    }

    /**
     * See https://github.com/Kotlin/kotlinx.coroutines/issues/1713
     */
    @Test
    fun testChannelBroadcastLazyCancel() = runTest {
        expect(1)
        val a = produce {
            expect(3)
            assertFailsWith<CancellationException> { send("MSG") }
            expect(5)
        }
        expect(2)
        yield() // to produce
        val b = a.broadcast()
        b.cancel()
        expect(4)
        yield() // to abort produce
        assertTrue(a.isClosedForReceive) // the source channel was consumed
        finish(6)
    }

    @Test
    fun testChannelBroadcastLazyClose() = runTest {
        expect(1)
        val a = produce {
            expect(3)
            send("MSG")
            expectUnreached() // is not executed, because send is cancelled
        }
        expect(2)
        yield() // to produce
        val b = a.broadcast()
        b.close()
        expect(4)
        yield() // to abort produce
        assertTrue(a.isClosedForReceive) // the source channel was consumed
        finish(5)
    }

    @Test
    fun testChannelBroadcastEagerCancel() = runTest {
        expect(1)
        val a = produce<Unit> {
            expect(3)
            yield() // back to main
            expectUnreached() // will be cancelled
        }
        expect(2)
        val b = a.broadcast(start = CoroutineStart.DEFAULT)
        yield() // to produce
        expect(4)
        b.cancel()
        yield() // to produce (cancelled)
        assertTrue(a.isClosedForReceive) // the source channel was consumed
        finish(5)
    }

    @Test
    fun testChannelBroadcastEagerClose() = runTest {
        expect(1)
        val a = produce<Unit> {
            expect(3)
            yield() // back to main
            // shall eventually get cancelled
            assertFailsWith<CancellationException> {
                while (true) { send(Unit) }
            }
        }
        expect(2)
        val b = a.broadcast(start = CoroutineStart.DEFAULT)
        yield() // to produce
        expect(4)
        b.close()
        yield() // to produce (closed)
        assertTrue(a.isClosedForReceive) // the source channel was consumed
        finish(5)
    }

    @Test
    fun testBroadcastCloseWithException() = runTest {
        expect(1)
        val b = broadcast(NonCancellable, capacity = 1) {
            expect(2)
            send(1)
            expect(3)
            send(2) // suspends
            expect(5)
            // additional attempts to send fail
            assertFailsWith<TestException> { send(3) }
        }
        val sub = b.openSubscription()
        yield() // into broadcast
        expect(4)
        b.close(TestException()) // close broadcast channel with exception
        assertTrue(b.isClosedForSend) // sub was also closed
        assertEquals(1, sub.receive()) // 1st element received
        assertEquals(2, sub.receive()) // 2nd element received
        assertFailsWith<TestException> { sub.receive() } // then closed with exception
        yield() // to cancel broadcast
        finish(6)
    }
}