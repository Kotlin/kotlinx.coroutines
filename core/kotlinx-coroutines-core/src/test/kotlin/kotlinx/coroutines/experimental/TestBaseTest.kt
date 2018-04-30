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

import org.junit.*

class TestBaseTest : TestBase() {
    @Test
    fun testThreadsShutdown() {
        val SHUTDOWN_TIMEOUT = 1_000L
        repeat(1000 * stressTestMultiplier) { _ ->
            CommonPool.usePrivatePool()
            val threadsBefore = currentThreads()
            runBlocking {
                val sub = launch(DefaultDispatcher) {
                    delay(10000000L)
                }
                sub.cancel()
                sub.join()
            }
            CommonPool.shutdown(SHUTDOWN_TIMEOUT)
            DefaultExecutor.shutdown(SHUTDOWN_TIMEOUT)
            checkTestThreads(threadsBefore)
        }

    }
}