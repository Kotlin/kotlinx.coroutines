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

class ConflatedChannelTest : TestBase() {
    @Test
    fun testBasicConflationOfferPoll() {
        val q = ConflatedChannel<Int>()
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
        val q = ConflatedChannel<Int>()
        q.send(1)
        q.close() // shall conflate sent item and become closed
        assertNull(q.receiveOrNull())
    }

    @Test
    fun testConflationSendReceive() = runTest {
        val q = ConflatedChannel<Int>()
        expect(1)
        launch(coroutineContext) { // receiver coroutine
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
        val q = ConflatedChannel<Int>()
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
        val channel = ConflatedChannel<Int>()
        channel.cancel(TestException())
        channel.receiveOrNull()
    }

    private class TestException : Exception()
}
