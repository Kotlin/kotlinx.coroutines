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
import org.junit.Assert.*
import org.junit.Test

class ArrayChannelTest : TestBase() {
    @Test
    fun testSimple() = runBlocking {
        val q = ArrayChannel<Int>(1)
        check(q.isEmpty && !q.isFull)
        expect(1)
        val sender = launch(coroutineContext) {
            expect(4)
            q.send(1) // success -- buffered
            check(!q.isEmpty && q.isFull)
            expect(5)
            q.send(2) // suspends (buffer full)
            expect(9)
        }
        expect(2)
        val receiver = launch(coroutineContext) {
            expect(6)
            check(q.receive() == 1) // does not suspend -- took from buffer
            check(!q.isEmpty && q.isFull) // waiting sender's element moved to buffer
            expect(7)
            check(q.receive() == 2) // does not suspend (takes from sender)
            expect(8)
        }
        expect(3)
        sender.join()
        receiver.join()
        check(q.isEmpty && !q.isFull)
        finish(10)
    }

    @Test
    fun testStress() = runBlocking {
        val n = 100_000
        val q = ArrayChannel<Int>(1)
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
    fun testClosedBufferedReceiveOrNull() = runBlocking {
        val q = ArrayChannel<Int>(1)
        check(q.isEmpty && !q.isFull && !q.isClosedForSend && !q.isClosedForReceive)
        expect(1)
        launch(coroutineContext) {
            expect(5)
            check(!q.isEmpty && !q.isFull && q.isClosedForSend && !q.isClosedForReceive)
            assertEquals(42, q.receiveOrNull())
            expect(6)
            check(!q.isEmpty && !q.isFull && q.isClosedForSend && q.isClosedForReceive)
            assertEquals(null, q.receiveOrNull())
            expect(7)
        }
        expect(2)
        q.send(42) // buffers
        expect(3)
        q.close() // goes on
        expect(4)
        check(!q.isEmpty && !q.isFull && q.isClosedForSend && !q.isClosedForReceive)
        yield()
        check(!q.isEmpty && !q.isFull && q.isClosedForSend && q.isClosedForReceive)
        finish(8)
    }

    @Test
    fun testClosedExceptions() = runBlocking {
        val q = ArrayChannel<Int>(1)
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
        val q = ArrayChannel<Int>(1)
        assertTrue(q.offer(1))
        expect(1)
        launch(coroutineContext) {
            expect(3)
            assertEquals(1, q.poll())
            expect(4)
            assertEquals(null, q.poll())
            expect(5)
            assertEquals(2, q.receive()) // suspends
            expect(9)
            assertEquals(3, q.poll())
            expect(10)
            assertEquals(null, q.poll())
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
    fun testConsumeAll() = runBlocking {
        val q = ArrayChannel<Int>(5)
        for (i in 1..10) {
            if (i <= 5) {
                expect(i)
                q.send(i) // shall buffer
            } else {
                launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
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
        check(q.receiveOrNull() == null)
        finish(12)
    }
}