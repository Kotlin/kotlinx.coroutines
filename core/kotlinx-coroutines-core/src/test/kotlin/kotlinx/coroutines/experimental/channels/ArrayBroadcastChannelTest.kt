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
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import kotlin.coroutines.experimental.*

class ArrayBroadcastChannelTest : TestBase() {
    @Test
    fun testBasic() = runBlocking<Unit> {
        expect(1)
        val broadcast = ArrayBroadcastChannel<Int>(1)
        assertThat(broadcast.isClosedForSend, IsEqual(false))
        val first = broadcast.openSubscription()
        launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
            expect(2)
            assertThat(first.receive(), IsEqual(1)) // suspends
            assertThat(first.isClosedForReceive, IsEqual(false))
            expect(5)
            assertThat(first.receive(), IsEqual(2)) // suspends
            assertThat(first.isClosedForReceive, IsEqual(false))
            expect(10)
            assertThat(first.receiveOrNull(), IsNull()) // suspends
            assertThat(first.isClosedForReceive, IsEqual(true))
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
            assertThat(second.receive(), IsEqual(2)) // suspends
            assertThat(second.isClosedForReceive, IsEqual(false))
            expect(11)
            assertThat(second.receiveOrNull(), IsNull()) // suspends
            assertThat(second.isClosedForReceive, IsEqual(true))
            expect(15)
        }
        expect(8)
        broadcast.send(2)
        expect(9)
        yield() // to first & second receivers
        expect(12)
        broadcast.close()
        expect(13)
        assertThat(broadcast.isClosedForSend, IsEqual(true))
        yield() // to first & second receivers
        finish(16)
    }

    @Test
    fun testSendSuspend() = runBlocking {
        expect(1)
        val broadcast = ArrayBroadcastChannel<Int>(1)
        val first = broadcast.openSubscription()
        launch(coroutineContext) {
            expect(4)
            assertThat(first.receive(), IsEqual(1))
            expect(5)
            assertThat(first.receive(), IsEqual(2))
            expect(6)
        }
        expect(2)
        broadcast.send(1) // puts to buffer, receiver not running yet
        expect(3)
        broadcast.send(2) // suspends
        finish(7)
    }

    @Test
    fun testConcurrentSendCompletion() = runBlocking {
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
        assertThat(sub.isClosedForReceive, IsEqual(false))
        for (x in 1..3)
            assertThat(sub.receiveOrNull(), IsEqual(x))
        // and receive close signal
        assertThat(sub.receiveOrNull(), IsNull())
        assertThat(sub.isClosedForReceive, IsEqual(true))
        finish(7)
    }

    @Test
    fun testForgetUnsubscribed() = runBlocking {
        expect(1)
        val broadcast = ArrayBroadcastChannel<Int>(1)
        broadcast.send(1)
        broadcast.send(2)
        broadcast.send(3)
        expect(2) // should not suspend anywhere above
        val sub = broadcast.openSubscription()
        launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
            expect(3)
            assertThat(sub.receive(), IsEqual(4)) // suspends
            expect(5)
        }
        expect(4)
        broadcast.send(4) // sends
        yield()
        finish(6)
    }

    @Test
    fun testReceiveFullAfterClose() = runBlocking<Unit> {
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
    fun testCloseSubDuringIteration() = runBlocking<Unit> {
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
                sub.cancel()
            }
        }
        check(expected == 2)
    }

    @Test
    fun testReceiveFromClosedSub() = runTest(
        expected = { it is ClosedReceiveChannelException }
    ) {
        val channel = BroadcastChannel<Int>(1)
        val sub = channel.openSubscription()
        assertFalse(sub.isClosedForReceive)
        sub.cancel()
        assertTrue(sub.isClosedForReceive)
        sub.receive()
    }
}