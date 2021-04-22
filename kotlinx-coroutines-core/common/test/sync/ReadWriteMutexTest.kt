/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.coroutines.*
import kotlin.test.*

class ReadWriteMutexTest : TestBase() {
    @Test
    fun simpleSingleCoroutineTest() = runTest {
        val m = ReadWriteMutex()
        m.readLock()
        m.readLock()
        m.readUnlock()
        m.readUnlock()
        m.write.lock()
        m.write.unlock()
        m.readLock()
    }

    @Test
    fun multipleCoroutinesTest() = runTest {
        val m = ReadWriteMutex()
        m.readLock()
        expect(1)
        launch {
            expect(2)
            m.readLock()
            expect(3)
        }
        yield()
        expect(4)
        launch {
            expect(5)
            m.write.lock()
            expect(8)
        }
        yield()
        expect(6)
        m.readUnlock()
        yield()
        expect(7)
        m.readUnlock()
        yield()
        finish(9)
    }

    @Test
    fun acquireReadSucceedsAfterCancelledAcquireWrite() = runTest {
        val m = ReadWriteMutex()
        m.readLock()
        val wJob = launch {
            expect(1)
            m.write.lock()
            expectUnreached()
        }
        yield()
        expect(2)
        wJob.cancel()
        launch {
            expect(3)
            m.readLock()
            expect(4)
        }
        yield()
        finish(5)
    }
}