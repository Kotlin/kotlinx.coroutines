/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.sync

import kotlinx.coroutines.experimental.*
import kotlin.test.*

class MutexStressTest : TestBase() {
    @Test
    fun testStress() = runTest {
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
        println("Shared value = $shared")
        assertEquals(n * k, shared)
    }
}