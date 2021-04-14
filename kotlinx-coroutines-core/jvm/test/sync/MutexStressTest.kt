/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import kotlin.test.*

class MutexStressTest : TestBase() {
    @Test
    fun testStress() = runBlocking(Dispatchers.Default) {
        val n = 1000 * stressTestMultiplier
        val k = 100
        var shared = 0
        val mutex = Mutex()
        val jobs = List(n) {
            launch {
                repeat(k) {
                    mutex.lock()
                    shared++
                    mutex.unlock()
                }
            }
        }
        jobs.forEach { it.join() }
        assertEquals(n * k, shared)
    }

    @Test
    fun stressUnlockCancelRace() = runTest {
        val n = 10_000 * stressTestMultiplier
        val mutex = Mutex(true) // create a locked mutex
        newSingleThreadContext("SemaphoreStressTest").use { pool ->
            repeat (n) {
                // Initially, we hold the lock and no one else can `lock`,
                // otherwise it's a bug.
                assertTrue(mutex.isLocked)
                var job1EnteredCriticalSection = false
                val job1 = launch(start = CoroutineStart.UNDISPATCHED) {
                    mutex.lock()
                    job1EnteredCriticalSection = true
                    mutex.unlock()
                }
                // check that `job1` didn't finish the call to `acquire()`
                assertEquals(false, job1EnteredCriticalSection)
                val job2 = launch(pool) {
                    mutex.unlock()
                }
                // Because `job2` executes in a separate thread, this
                // cancellation races with the call to `unlock()`.
                job1.cancelAndJoin()
                job2.join()
                assertFalse(mutex.isLocked)
                mutex.lock()
            }
        }
    }

    @Test
    fun stressUnlockCancelRaceWithSelect() = runTest {
        val n = 10_000 * stressTestMultiplier
        val mutex = Mutex(true) // create a locked mutex
        newSingleThreadContext("SemaphoreStressTest").use { pool ->
            repeat (n) {
                // Initially, we hold the lock and no one else can `lock`,
                // otherwise it's a bug.
                assertTrue(mutex.isLocked)
                var job1EnteredCriticalSection = false
                val job1 = launch(start = CoroutineStart.UNDISPATCHED) {
                    select<Unit> {
                        mutex.onLock {
                            job1EnteredCriticalSection = true
                            mutex.unlock()
                        }
                    }
                }
                // check that `job1` didn't finish the call to `acquire()`
                assertEquals(false, job1EnteredCriticalSection)
                val job2 = launch(pool) {
                    mutex.unlock()
                }
                // Because `job2` executes in a separate thread, this
                // cancellation races with the call to `unlock()`.
                job1.cancelAndJoin()
                job2.join()
                assertFalse(mutex.isLocked)
                mutex.lock()
            }
        }
    }

    @Test
    fun testShouldBeUnlockedOnCancellation() = runTest {
        val mutex = Mutex()
        val n = 1000 * stressTestMultiplier
        repeat(n) {
            val job = launch(Dispatchers.Default) {
                mutex.lock()
                mutex.unlock()
            }
            mutex.withLock {
                job.cancel()
            }
            job.join()
            assertFalse { mutex.isLocked }
        }
    }
}
