/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.test.*

class JobStressTest : TestBase() {
    @Test
    fun testMemoryRelease() {
        val job = Job()
        val n = 10_000_000 * stressTestMultiplier
        var fireCount = 0
        for (i in 0 until n) job.invokeOnCompletion { fireCount++ }.dispose()
    }
}