/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class ArrayBroadcastChannelTest : TestBase() {

    @Test
    fun testBasic() = runTest {
        expect(1)
        val broadcast = ArrayBroadcastChannel<Int>(1)
        assertFalse(broadcast.isClosedForSend)
        val first = broadcast.openSubscription()
        launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
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
        launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
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
        val broadcast = ArrayBroadcastChannel<Int>(1)
        val first = broadcast.openSubscription()
        launch(coroutineContext) {
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
        val broadcast = ArrayBroadcastChannel<Int>(1)
        val sub = broadcast.openSubscription()
        // launch 3 concurrent senders (one goes buffer, two other suspend)
        for (x in 1..3) {
            launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
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
        val broadcast = ArrayBroadcastChannel<Int>(1)
        broadcast.send(1)
        broadcast.send(2)
        broadcast.send(3)
        expect(2) // should not suspend anywhere above
        val sub = broadcast.openSubscription()
        launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
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
        launch(coroutineContext) {
            for (x in 1..5) channel.send(x)
            channel.close()
        }
        // start consuming
        val sub = channel.openSubscription()
        var expected = 0
        sub.consumeEach {
            check(it == ++expected)
            if (it == 2) {
                sub.close()
            }
        }
        check(expected == 2)
    }

    @Test
    fun testReceiveFromClosedSub() = runTest({ it is ClosedReceiveChannelException }) {
        val channel = BroadcastChannel<Int>(1)
        val sub = channel.openSubscription()
        assertFalse(sub.isClosedForReceive)
        sub.close()
        assertTrue(sub.isClosedForReceive)
        sub.receive()
    }
}
