/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.*

class TestBaseTest : TestBase() {
    @Test
    fun testThreadsShutdown() {
        repeat(1000 * stressTestMultiplier) { _ ->
            initPoolsBeforeTest()
            val threadsBefore = currentThreads()
            runBlocking {
                val sub = launch {
                    delay(10000000L)
                }
                sub.cancel()
                sub.join()
            }
            shutdownPoolsAfterTest()
            checkTestThreads(threadsBefore)
        }

    }
}