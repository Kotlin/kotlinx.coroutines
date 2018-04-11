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

package kotlinx.coroutines.experimental.sync

import kotlinx.coroutines.experimental.*
import kotlin.test.*
import kotlin.coroutines.experimental.*

class MutexTest : TestBase() {
    @Test
    fun testSimple() = runTest {
        val mutex = Mutex()
        expect(1)
        launch(coroutineContext) {
            expect(4)
            mutex.lock() // suspends
            expect(7) // now got lock
            mutex.unlock()
            expect(8)
        }
        expect(2)
        mutex.lock() // locked
        expect(3)
        yield() // yield to child
        expect(5)
        mutex.unlock()
        expect(6)
        yield() // now child has lock
        finish(9)
    }

    @Test
    fun tryLockTest() {
        val mutex = Mutex()
        assertFalse(mutex.isLocked)
        assertTrue(mutex.tryLock())
        assertTrue(mutex.isLocked)
        assertFalse(mutex.tryLock())
        assertTrue(mutex.isLocked)
        mutex.unlock()
        assertFalse(mutex.isLocked)
        assertTrue(mutex.tryLock())
        assertTrue(mutex.isLocked)
        assertFalse(mutex.tryLock())
        assertTrue(mutex.isLocked)
        mutex.unlock()
        assertFalse(mutex.isLocked)
    }

    @Test
    fun withLockTest() = runTest {
        val mutex = Mutex()
        assertFalse(mutex.isLocked)
        mutex.withLock {
            assertTrue(mutex.isLocked)
        }
        assertFalse(mutex.isLocked)
    }

    @Test
    fun testUnconfinedStackOverflow() {
        val waiters = 10000
        val mutex = Mutex(true)
        var done = 0
        repeat(waiters) {
            launch(Unconfined) {  // a lot of unconfined waiters
                mutex.withLock {
                    done++
                }
            }
        }
        mutex.unlock() // should not produce StackOverflowError
        assertEquals(waiters, done)
    }

    @Test
    fun holdLock() = runTest {
        val mutex = Mutex()
        val firstOwner = Any()
        val secondOwner = Any()

        // no lock
        assertFalse(mutex.holdsLock(firstOwner))
        assertFalse(mutex.holdsLock(secondOwner))

        // owner firstOwner
        mutex.lock(firstOwner)
        val secondLockJob = launch {
            mutex.lock(secondOwner)
        }

        assertTrue(mutex.holdsLock(firstOwner))
        assertFalse(mutex.holdsLock(secondOwner))

        // owner secondOwner
        mutex.unlock(firstOwner)
        secondLockJob.join()

        assertFalse(mutex.holdsLock(firstOwner))
        assertTrue(mutex.holdsLock(secondOwner))

        mutex.unlock(secondOwner)

        // no lock
        assertFalse(mutex.holdsLock(firstOwner))
        assertFalse(mutex.holdsLock(secondOwner))
    }
}