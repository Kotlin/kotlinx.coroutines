/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import org.junit.runner.*
import org.junit.runners.*
import kotlin.test.*

@RunWith(Parameterized::class)
class LockFreeTaskQueueTest(
    private val singleConsumer: Boolean
) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "singleConsumer={0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = listOf(
            arrayOf<Any>(false),
            arrayOf<Any>(true)
        )
    }

    @Test
    fun testBasic() {
        val q = LockFreeTaskQueue<Int>(singleConsumer)
        assertTrue(q.isEmpty)
        assertEquals(0, q.size)
        assertTrue(q.addLast(1))
        assertFalse(q.isEmpty)
        assertEquals(1, q.size)
        assertTrue(q.addLast(2))
        assertFalse(q.isEmpty)
        assertEquals(2, q.size)
        assertTrue(q.addLast(3))
        assertFalse(q.isEmpty)
        assertEquals(3, q.size)
        assertEquals(1, q.removeFirstOrNull())
        assertFalse(q.isEmpty)
        assertEquals(2, q.size)
        assertEquals(2, q.removeFirstOrNull())
        assertFalse(q.isEmpty)
        assertEquals(1, q.size)
        assertTrue(q.addLast(4))
        assertFalse(q.isEmpty)
        assertEquals(2, q.size)
        q.close()
        assertFalse(q.isEmpty)
        assertEquals(2, q.size)
        assertFalse(q.addLast(5))
        assertFalse(q.isEmpty)
        assertEquals(2, q.size)
        assertEquals(3, q.removeFirstOrNull())
        assertFalse(q.isEmpty)
        assertEquals(1, q.size)
        assertEquals(4, q.removeFirstOrNull())
        assertTrue(q.isEmpty)
        assertEquals(0, q.size)
    }

    @Test
    fun testCopyGrow() {
        val n = 1000 * stressTestMultiplier
        val q = LockFreeTaskQueue<Int>(singleConsumer)
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