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