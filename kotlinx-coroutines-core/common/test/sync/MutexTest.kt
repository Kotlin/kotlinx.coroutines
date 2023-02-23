/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import kotlin.test.*

class MutexTest : TestBase() {
    @Test
    fun testSimple() = runTest {
        val mutex = Mutex()
        expect(1)
        launch {
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
            GlobalScope.launch(Dispatchers.Unconfined) {  // a lot of unconfined waiters
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

    @Test
    fun testUnlockWithNullOwner() {
        val owner = Any()
        val mutex = Mutex()
        assertTrue(mutex.tryLock(owner))
        assertFailsWith<IllegalStateException> { mutex.unlock(Any()) }
        mutex.unlock(null)
        assertFalse(mutex.holdsLock(owner))
        assertFalse(mutex.isLocked)
    }

    @Test
    fun testUnlockWithoutOwnerWithLockedQueue() = runTest {
        val owner = Any()
        val owner2 = Any()
        val mutex = Mutex()
        assertTrue(mutex.tryLock(owner))
        expect(1)
        launch {
            expect(2)
            mutex.lock(owner2)
        }
        yield()
        expect(3)
        assertFailsWith<IllegalStateException> { mutex.unlock(owner2) }
        mutex.unlock()
        assertFalse(mutex.holdsLock(owner))
        assertTrue(mutex.holdsLock(owner2))
        finish(4)
    }

    @Test
    fun testIllegalStateInvariant() = runTest {
        val mutex = Mutex()
        val owner = Any()
        assertTrue(mutex.tryLock(owner))
        assertFailsWith<IllegalStateException> { mutex.tryLock(owner) }
        assertFailsWith<IllegalStateException> { mutex.lock(owner) }
        assertFailsWith<IllegalStateException> { select { mutex.onLock(owner) {} } }
    }
}
