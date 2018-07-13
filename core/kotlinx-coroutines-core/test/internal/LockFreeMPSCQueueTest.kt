/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.test.*

class LockFreeMPSCQueueTest : TestBase() {
    @Test
    fun testBasic() {
        val q = LockFreeMPSCQueue<Int>()
        assertTrue(q.isEmpty)
        assertTrue(q.addLast(1))
        assertFalse(q.isEmpty)
        assertTrue(q.addLast(2))
        assertFalse(q.isEmpty)
        assertTrue(q.addLast(3))
        assertFalse(q.isEmpty)
        assertEquals(1, q.removeFirstOrNull())
        assertFalse(q.isEmpty)
        assertEquals(2, q.removeFirstOrNull())
        assertFalse(q.isEmpty)
        assertTrue(q.addLast(4))
        q.close()
        assertFalse(q.isEmpty)
        assertFalse(q.addLast(5))
        assertFalse(q.isEmpty)
        assertEquals(3, q.removeFirstOrNull())
        assertFalse(q.isEmpty)
        assertEquals(4, q.removeFirstOrNull())
        assertTrue(q.isEmpty)
    }

    @Test
    fun testCopyGrow() {
        val n = 1000 * stressTestMultiplier
        val q = LockFreeMPSCQueue<Int>()
        assertTrue(q.isEmpty)
        repeat(n) { i ->
            assertTrue(q.addLast(i))
            assertFalse(q.isEmpty)
        }
        repeat(n) { i ->
            assertEquals(i, q.removeFirstOrNull())
        }
        assertTrue(q.isEmpty)
    }
}