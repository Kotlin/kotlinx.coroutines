/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.selects

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.sync.*
import kotlin.test.*

class SelectMutexStressTest : TestBase() {
    @Test
    fun testSelectCancelledResourceRelease() = runTest {
        val n = 1_000 * stressTestMultiplier
        val mutex = Mutex(true) as MutexImpl // locked
        expect(1)
        repeat(n) { i ->
            val job = launch(kotlin.coroutines.experimental.coroutineContext) {
                expect(i + 2)
                select<Unit> {
                    mutex.onLock {
                        expectUnreached() // never able to lock
                    }
                }
            }
            yield() // to the launched job, so that it suspends
            job.cancel() // cancel the job and select
            yield() // so it can cleanup after itself
        }
        assertTrue(mutex.isLocked)
        assertTrue(mutex.isLockedEmptyQueueState)
        finish(n + 2)
    }
}