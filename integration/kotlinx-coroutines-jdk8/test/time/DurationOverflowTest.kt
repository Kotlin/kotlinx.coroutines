/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.time

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import org.junit.Test
import java.time.*
import java.time.temporal.*
import kotlin.test.*

class DurationOverflowTest : TestBase() {

    private val durations = ChronoUnit.values().map { it.duration }

    @Test
    fun testDelay() = runTest {
        var counter = 0
        for (duration in durations) {
            expect(++counter)
            delay(duration.negated()) // Instant bail out from negative values
            launch(start = CoroutineStart.UNDISPATCHED) {
                expect(++counter)
                delay(duration)
            }.cancelAndJoin()
            expect(++counter)
        }

        finish(++counter)
    }

    @Test
    fun testOnTimeout() = runTest {
        for (duration in durations) {
            // Does not crash on overflows
            select<Unit> {
                onTimeout(duration) {}
                onTimeout(duration.negated()) {}
            }
        }
    }

    @Test
    fun testWithTimeout() = runTest {
        for (duration in durations) {
            withTimeout(duration) {}
        }
    }

    @Test
    fun testWithTimeoutOrNull() = runTest {
        for (duration in durations) {
            withTimeoutOrNull(duration) {}
        }
    }

    @Test
    fun testWithTimeoutOrNullNegativeDuration() = runTest {
        val result = withTimeoutOrNull(Duration.ofSeconds(1).negated()) {
            1
        }

        assertNull(result)
    }

}
