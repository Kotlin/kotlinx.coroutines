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
        assertEquals(null, result)
    }
}