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

package kotlinx.coroutines.experimental

import kotlin.test.*

class MessageQueueTest {
    private var scheduled = false
    private val processed = mutableListOf<Int>()

    private val queue = object : MessageQueue() {
        override fun schedule() {
            assertFalse(scheduled)
            scheduled = true
        }
    }

    inner class Box(val i: Int): Runnable {
        override fun run() {
            processed += i
        }
    }

    inner class ReBox(val i: Int): Runnable {
        override fun run() {
            processed += i
            queue.enqueue(Box(10 + i))
        }
    }

    @Test
    fun testBasic() {
        assertTrue(queue.isEmpty)
        queue.enqueue(Box(1))
        assertFalse(queue.isEmpty)
        assertTrue(scheduled)
        queue.enqueue(Box(2))
        assertFalse(queue.isEmpty)
        scheduled = false
        queue.process()
        assertEquals(listOf(1, 2), processed)
        assertFalse(scheduled)
        assertTrue(queue.isEmpty)
    }

    @Test fun testRescheduleFromProcess()  {
        assertTrue(queue.isEmpty)
        queue.enqueue(ReBox(1))
        assertFalse(queue.isEmpty)
        assertTrue(scheduled)
        queue.enqueue(ReBox(2))
        assertFalse(queue.isEmpty)
        scheduled = false
        queue.process()
        assertEquals(listOf(1, 2, 11, 12), processed)
        assertFalse(scheduled)
        assertTrue(queue.isEmpty)
    }

    @Test
    fun testResizeAndWrap() {
        repeat(10) { phase ->
            val n = 10 * (phase + 1)
            assertTrue(queue.isEmpty)
            repeat(n) {
                queue.enqueue(Box(it))
                assertFalse(queue.isEmpty)
                assertTrue(scheduled)
            }
            var countYields = 0
            while (scheduled) {
                scheduled = false
                queue.process()
                countYields++
            }
            assertEquals(List(n) { it }, processed)
            assertEquals((n + queue.yieldEvery - 1) / queue.yieldEvery, countYields)
            processed.clear()
        }
    }
}