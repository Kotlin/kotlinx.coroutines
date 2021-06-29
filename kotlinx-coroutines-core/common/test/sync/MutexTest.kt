/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.coroutines.*
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
    fun testTryLock() {
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
    fun testWithLock() = runTest {
        val mutex = Mutex()
        assertFalse(mutex.isLocked)
        mutex.withLock {
            assertTrue(mutex.isLocked)
        }
        assertFalse(mutex.isLocked)
    }

    @Test
    fun testHoldsLock() = runTest {
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
    fun testUnlockWithoutOwner() {
        val owner = Any()
        val mutex = Mutex()
        assertTrue(mutex.tryLock(owner))
        assertFailsWith<IllegalStateException> { mutex.unlock(Any()) }
        assertFailsWith<IllegalStateException> { mutex.unlock() }
        assertFailsWith<IllegalStateException> { mutex.unlock(null) }
        assertTrue(mutex.holdsLock(owner))
        mutex.unlock(owner)
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
        assertFailsWith<IllegalStateException> { mutex.unlock() }
        assertFailsWith<IllegalStateException> { mutex.unlock(null) }
        assertTrue(mutex.holdsLock(owner))
        mutex.unlock(owner)
        assertTrue(mutex.isLocked)
        assertTrue(mutex.holdsLock(owner2))
        finish(4)
    }
}
