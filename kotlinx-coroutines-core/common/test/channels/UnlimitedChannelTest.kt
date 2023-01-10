/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class UnlimitedChannelTest : TestBase() {
    @Test
    fun testBasic() = runTest {
        val c = Channel<Int>(Channel.UNLIMITED)
        c.send(1)
        assertTrue(c.trySend(2).isSuccess)
        c.send(3)
        check(c.close())
        check(!c.close())
        assertEquals(1, c.receive())
        assertEquals(2, c.tryReceive().getOrNull())
        assertEquals(3, c.receiveCatching().getOrNull())
        assertNull(c.receiveCatching().getOrNull())
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
        assertFailsWith<CancellationException> { q.receive() }
    }

    @Test
    fun testCancelWithCause() = runTest({ it is TestCancellationException }) {
        val channel = Channel<Int>(Channel.UNLIMITED)
        channel.cancel(TestCancellationException())
        channel.receive()
    }
}
