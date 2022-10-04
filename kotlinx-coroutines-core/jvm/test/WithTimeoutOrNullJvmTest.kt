/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class WithTimeoutOrNullJvmTest : TestBase() {
    @Test
    fun testOuterTimeoutFiredBeforeInner() = runTest {
        val result = withTimeoutOrNull(100) {
            Thread.sleep(200) // wait enough for outer timeout to fire
            withContext(NonCancellable) { yield() } // give an event loop a chance to run and process that cancellation
            withTimeoutOrNull(100) {
                yield() // will cancel because of outer timeout
                expectUnreached()
            }
            expectUnreached() // should not be reached, because it is outer timeout
        }
        // outer timeout results in null
        assertNull(result)
    }

    @Test
    fun testIgnoredTimeout() = runTest {
        val value = withTimeout(1) {
            Thread.sleep(10)
            42
        }

        assertEquals(42, value)
    }

    @Test
    fun testIgnoredTimeoutOnNull() = runTest {
        val value = withTimeoutOrNull(1) {
            Thread.sleep(10)
            42
        }

        assertEquals(42, value)
    }

    @Test
    fun testIgnoredTimeoutOnNullThrowsCancellation() = runTest {
        try {
            withTimeoutOrNull(1) {
                expect(1)
                Thread.sleep(10)
                throw CancellationException()
            }
            expectUnreached()
        } catch (e: CancellationException) {
            finish(2)
        }
    }

    @Test
    fun testIgnoredTimeoutOnNullThrowsOnYield() = runTest {
        val value = withTimeoutOrNull(1) {
            Thread.sleep(75)
            yield()
        }
        assertNull(value)
    }
}
