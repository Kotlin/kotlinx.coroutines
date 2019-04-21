/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.*

/**
 * Test a race between job failure and join.
 *
 * See [#1123](https://github.com/Kotlin/kotlinx.coroutines/issues/1123).
 */
class JobStructuredJoinStressTest : TestBase() {
    private val nRepeats = 1_000 * stressTestMultiplier

    @Test
    fun testStress() {
        repeat(nRepeats) {
            assertFailsWith<TestException> {
                runBlocking {
                    // launch in background
                    val job = launch(Dispatchers.Default) {
                        throw TestException("OK") // crash
                    }
                    assertFailsWith<CancellationException> {
                        job.join()
                    }
                }
            }
        }
    }
}