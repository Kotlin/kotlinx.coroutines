/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.time

import kotlinx.coroutines.*
import org.junit.Test
import java.time.*
import kotlin.test.*

class WithTimeoutTest : TestBase() {

    @Test
    fun testWithTimeout() = runTest {
        expect(1)
        val result = withTimeout(Duration.ofMillis(10_000)) {
            expect(2)
            delay(Duration.ofNanos(1))
            expect(3)
            42
        }

        assertEquals(42, result)
        finish(4)
    }

    @Test
    fun testWithTimeoutOrNull() = runTest {
        expect(1)
        val result = withTimeoutOrNull(Duration.ofMillis(10_000)) {
            expect(2)
            delay(Duration.ofNanos(1))
            expect(3)
            42
        }

        assertEquals(42, result)
        finish(4)
    }

    @Test
    fun testWithTimeoutOrNullExceeded() = runTest {
        expect(1)
        val result = withTimeoutOrNull(Duration.ofMillis(3)) {
            expect(2)
            delay(Duration.ofSeconds(Long.MAX_VALUE))
            expectUnreached()
        }

        assertNull(result)
        finish(3)
    }

    @Test
    fun testWithTimeoutExceeded() = runTest {
        expect(1)
        try {
            withTimeout(Duration.ofMillis(3)) {
                expect(2)
                delay(Duration.ofSeconds(Long.MAX_VALUE))
                expectUnreached()
            }
        } catch (e: TimeoutCancellationException) {
            finish(3)
        }
    }
}