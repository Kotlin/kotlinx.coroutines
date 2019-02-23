/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.time

import kotlinx.coroutines.*
import org.hamcrest.core.*
import org.junit.*
import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.Job
import kotlinx.coroutines.selects.select
import java.time.temporal.ChronoUnit

class TimeTest : TestBase() {

    private val durations = ChronoUnit.values().map { it.duration }

    @Test
    fun testDelay() {
        runTest {
            for (duration in durations) {
                delay(duration.negated())

                launch(start = CoroutineStart.UNDISPATCHED) {
                    delay(duration)
                }
                        .cancel()
            }
        }
    }

    @Test
    fun testOnTimeout() {
        runTest {
            for (duration in durations) {
                select<Unit> {
                    onTimeout(duration) {}
                    onTimeout(duration.negated()) {}
                }
            }
        }
    }

    @Test
    fun testWithTimeout() {
        runTest {
            for (duration in durations) {
                withTimeout(duration) {}
            }
        }
    }

    @Test
    fun testWithTimeoutOrNull() {
        runTest {
            for (duration in durations) {
                withTimeoutOrNull(duration) {}
            }
        }
    }

}
