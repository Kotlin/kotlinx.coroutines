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

package kotlinx.coroutines.experimental.selects

import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import kotlinx.coroutines.experimental.sync.Mutex
import kotlinx.coroutines.experimental.sync.MutexImpl
import kotlinx.coroutines.experimental.yield
import org.junit.Assert.assertEquals
import org.junit.Assert.assertTrue
import org.junit.Test

class SelectMutexTest : TestBase() {
    @Test
    fun testSelectLock() = runBlocking<Unit> {
        val mutex = Mutex()
        expect(1)
        launch(context) { // ensure that it is not scheduled earlier than needed
            finish(4)
        }
        val res = select<String> {
            mutex.onLock {
                assertTrue(mutex.isLocked)
                expect(2)
                "OK"
            }
        }
        assertEquals("OK", res)
        expect(3)
    }

    @Test
    fun testSelectLockWait() = runBlocking<Unit> {
        val mutex = Mutex(true) // locked
        expect(1)
        launch(context) {
            expect(3)
            val res = select<String> { // will suspended
                mutex.onLock {
                    assertTrue(mutex.isLocked)
                    expect(6)
                    "OK"
                }
            }
            assertEquals("OK", res)
            expect(7)
        }
        expect(2)
        yield() // to launched coroutine
        expect(4)
        mutex.unlock()
        expect(5)
        yield() // to resumed select
        finish(8)
    }

    @Test
    fun testSelectCancelledResourceRelease() = runBlocking<Unit> {
        val n = 1_000 * stressTestMultiplier
        val mutex = Mutex(true) as MutexImpl // locked
        expect(1)
        repeat(n) { i ->
            val job = launch(context) {
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