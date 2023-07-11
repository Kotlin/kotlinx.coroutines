/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

class RunTestStressTest {
    /** Tests that notifications about asynchronous resumptions aren't lost. */
    @Test
    fun testRunTestActivityNotificationsRace() {
        val n = 1_000 * stressTestMultiplier
        for (i in 0 until n) {
            runTest {
                suspendCancellableCoroutine<Unit> { cont ->
                    thread {
                        cont.resume(Unit)
                    }
                }
            }
        }
    }
}