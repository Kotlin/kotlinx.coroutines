/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import org.junit.rules.*
import kotlin.test.*

class RunBlockingTestTimeTest : TestBase() { // I am really sorry for this name

    @get:Rule
    val timeout = Timeout.seconds(1)

    @Test
    fun testTimeAutoAdvance() = runBlockingTest {
        expect(1)
        longDelay()
        finish(2)
    }

    @Test
    fun testTimeAutoAdvanceFromCoroutine() = runBlockingTest {
        expect(1)
        val value = async {
            longDelay()
            239
        }
        assertEquals(239, value.await())
        finish(2)
    }

    @Test
    fun testWithTimeoutSuccessful() = runBlockingTest {
        expect(1)
        val value = withTimeoutOrNull(Long.MAX_VALUE) {
            expect(2)
            longDelay(Long.MAX_VALUE / 2)
            expect(3)
            42
        }
        assertEquals(42, value)
        finish(4)
    }

    @Test
    fun testWithTimeoutOrNull() = runBlockingTest {
        expect(1)
        val value = withTimeoutOrNull(Long.MAX_VALUE / 2) {
            expect(2)
            longDelay(Long.MAX_VALUE)
            expectUnreached()
            42
        }
        assertNull(value)
        finish(3)
    }

    @Test(expected = TimeoutCancellationException::class)
    fun testWithTimeout() = runBlockingTest {
        withTimeout(Long.MAX_VALUE / 2) {
            longDelay(Long.MAX_VALUE)
            expectUnreached()
            42
        }
        expectUnreached()
    }

    @Test
    fun testRelativeOrder() = runBlockingTest {
        expect(1)
        launch {
            longDelay(10_000)
            finish(4)
        }
        launch {
            longDelay(9_999)
            expect(3)
        }
        expect(2)
    }

    @Test
    fun testRelativeOrderFifo() = runBlockingTest {
        expect(1)
        launch {
            longDelay(10_000)
            expect(3)
        }
        launch {
            longDelay(10_000)
            finish(4)
        }
        expect(2)
    }

    private suspend fun longDelay(value: Long = Long.MAX_VALUE) { // To be sure it's not an extension on TCS
        delay(value)
    }
}
