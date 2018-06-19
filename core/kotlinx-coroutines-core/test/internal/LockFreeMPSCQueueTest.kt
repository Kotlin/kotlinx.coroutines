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

package kotlinx.coroutines.experimental.internal

import kotlinx.coroutines.experimental.*
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