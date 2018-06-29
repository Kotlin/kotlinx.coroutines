/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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