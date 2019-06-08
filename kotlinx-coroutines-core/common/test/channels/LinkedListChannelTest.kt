/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class LinkedListChannelTest : TestBase() {
    @Test
    fun testBasic() = runTest {
        val c = Channel<Int>(Channel.UNLIMITED)
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
        val q = Channel<Int>(Channel.UNLIMITED)
        for (i in 1..10) {
            q.send(i) // buffers
        }
        q.cancel()
        check(q.isClosedForSend)
        check(q.isClosedForReceive)
        assertFailsWith<CancellationException> { q.receiveOrNull() }
    }

    @Test
    fun testCancelWithCause() = runTest({ it is TestCancellationException }) {
        val channel = Channel<Int>(Channel.UNLIMITED)
        channel.cancel(TestCancellationException())
        channel.receiveOrNull()
    }
}
