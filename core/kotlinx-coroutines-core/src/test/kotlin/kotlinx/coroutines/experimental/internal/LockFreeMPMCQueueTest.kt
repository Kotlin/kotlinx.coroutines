/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

import kotlinx.coroutines.experimental.*
import org.junit.Test
import kotlin.test.*

class LockFreeMPMCQueueTest : TestBase() {
    @Test
    fun testBasic() {
        val q = LockFreeMPMCQueue<Node>()
        assertEquals(null, q.removeFistOrNull())
        assertTrue(q.isEmpty())
        q.addLast(Node(1))
        assertEquals(1, q.size)
        assertEquals(Node(1), q.removeFistOrNull())
        assertEquals(null, q.removeFistOrNull())
        assertTrue(q.isEmpty())
    }

    private data class Node(val v: Int) : LockFreeMPMCQueueNode<Node>()
}