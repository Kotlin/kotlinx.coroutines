/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*

class ChannelBufferOverflowTest : TestBase() {
    @Test
    fun testDropLatest() = runTest {
        val c = Channel<Int>(2, BufferOverflow.DROP_LATEST)
        assertTrue(c.offer(1))
        assertTrue(c.offer(2))
        assertTrue(c.offer(3)) // overflows, dropped
        c.send(4) // overflows dropped
        assertEquals(1, c.receive())
        assertTrue(c.offer(5))
        assertTrue(c.offer(6)) // overflows, dropped
        assertEquals(2, c.receive())
        assertEquals(5, c.receive())
        assertEquals(null, c.poll())
    }

    @Test
    fun testDropOldest() = runTest {
        val c = Channel<Int>(2, BufferOverflow.DROP_OLDEST)
        assertTrue(c.offer(1))
        assertTrue(c.offer(2))
        assertTrue(c.offer(3)) // overflows, keeps 2, 3
        c.send(4) // overflows, keeps 3, 4
        assertEquals(3, c.receive())
        assertTrue(c.offer(5))
        assertTrue(c.offer(6)) // overflows, keeps 5, 6
        assertEquals(5, c.receive())
        assertEquals(6, c.receive())
        assertEquals(null, c.poll())
    }
}