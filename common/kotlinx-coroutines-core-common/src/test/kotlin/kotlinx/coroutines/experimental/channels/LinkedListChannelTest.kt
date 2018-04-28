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
import kotlin.test.*

class LinkedListChannelTest : TestBase() {
    @Test
    fun testBasic() = runTest {
        val c = LinkedListChannel<Int>()
        c.send(1)
        check(c.offer(2))
        c.send(3)
        check(c.close())
        check(!c.close())
        assertEquals(1, c.receive())
        assertEquals(2, c.poll())
        assertEquals(3, c.receiveOrNull())
        assertNull(c.receiveOrNull())
    }

    @Test
    fun testConsumeAll() = runTest {
        val q = LinkedListChannel<Int>()
        for (i in 1..10) {
            q.send(i) // buffers
        }
        q.cancel()
        check(q.isClosedForSend)
        check(q.isClosedForReceive)
        check(q.receiveOrNull() == null)
    }

    @Test
    fun testCancelWithCause() = runTest({ it is TestException }) {
        val channel = LinkedListChannel<Int>()
        channel.cancel(TestException())
        channel.receiveOrNull()
    }

    private class TestException : Exception()
}
