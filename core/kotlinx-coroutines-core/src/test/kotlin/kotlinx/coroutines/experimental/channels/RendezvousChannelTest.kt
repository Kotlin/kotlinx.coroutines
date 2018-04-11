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
import java.io.IOException
import kotlin.coroutines.experimental.*

class RendezvousChannelTest : TestBase() {
    @Test
    fun testSimple() = runBlocking {
        val q = RendezvousChannel<Int>()
        check(q.isEmpty && q.isFull)
        expect(1)
        val sender = launch(coroutineContext) {
            expect(4)
            q.send(1) // suspend -- the first to come to rendezvous
            expect(7)
            q.send(2) // does not suspend -- receiver is there
            expect(8)
        }
        expect(2)
        val receiver = launch(coroutineContext) {
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
    fun testStress() = runBlocking {
        val n = 100_000
        val q = RendezvousChannel<Int>()
        val sender = launch(coroutineContext) {
            for (i in 1..n) q.send(i)
            expect(2)
        }
        val receiver = launch(coroutineContext) {
            for (i in 1..n) check(q.receive() == i)
            expect(3)
        }
        expect(1)
        sender.join()
        receiver.join()
        finish(4)
    }

    @Test
    fun testClosedReceiveOrNull() = runBlocking {
        val q = RendezvousChannel<Int>()
        check(q.isEmpty && q.isFull && !q.isClosedForSend && !q.isClosedForReceive)
        expect(1)
        launch(coroutineContext) {
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
    fun testClosedExceptions() = runBlocking {
        val q = RendezvousChannel<Int>()
        expect(1)
        launch(coroutineContext) {
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
    fun testOfferAndPool() = runBlocking {
        val q = RendezvousChannel<Int>()
        assertFalse(q.offer(1))
        expect(1)
        launch(coroutineContext) {
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
    fun testIteratorClosed() = runBlocking {
        val q = RendezvousChannel<Int>()
        expect(1)
        launch(coroutineContext) {
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
    fun testIteratorOne() = runBlocking {
        val q = RendezvousChannel<Int>()
        expect(1)
        launch(coroutineContext) {
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
    fun testIteratorOneWithYield() = runBlocking {
        val q = RendezvousChannel<Int>()
        expect(1)
        launch(coroutineContext) {
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
    fun testIteratorTwo() = runBlocking {
        val q = RendezvousChannel<Int>()
        expect(1)
        launch(coroutineContext) {
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
    fun testIteratorTwoWithYield() = runBlocking {
        val q = RendezvousChannel<Int>()
        expect(1)
        launch(coroutineContext) {
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
    fun testSuspendSendOnClosedChannel() = runBlocking<Unit> {
        val q = RendezvousChannel<Int>()
        expect(1)
        launch(coroutineContext) {
            expect(4)
            q.send(42) // suspend
            expect(11)
        }
        expect(2)
        launch(coroutineContext) {
            expect(5)
            q.close()
            expect(6)
        }
        expect(3)
        yield() // to sender
        expect(7)
        yield() // try to resume sender (it will not resume despite the close!)
        expect(8)
        assertThat(q.receiveOrNull(), IsEqual(42))
        expect(9)
        assertThat(q.receiveOrNull(), IsNull())
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
    fun testProduceBadClass() = runBlocking {
        val bad = BadClass()
        val c = produce(coroutineContext) {
            expect(1)
            send(bad)
        }
        assertTrue(c.receive() === bad)
        finish(2)
    }

    @Test
    fun testConsumeAll() = runBlocking {
        val q = RendezvousChannel<Int>()
        for (i in 1..10) {
            launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
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

    @Test(expected = IOException::class)
    fun testCancelWithCause() = runBlocking<Unit> {
        val channel = RendezvousChannel<Int>()
        channel.cancel(IOException())
        channel.receiveOrNull()
    }
}