/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class SetTimeoutDispatcherTest : TestBase() {
    @Test
    fun testDispatch() = runTest {
        launch(SetTimeoutDispatcher) {
            expect(1)
            launch {
                expect(3)
            }
            expect(2)
            yield()
            expect(4)
        }.join()
        finish(5)
    }

    @Test
    fun testDelay() = runTest {
        withContext(SetTimeoutDispatcher) {
            val job = launch(SetTimeoutDispatcher) {
                expect(2)
                delay(100)
                expect(4)
            }
            expect(1)
            yield() // Yield uses microtask, so should be in the same context
            expect(3)
            job.join()
            finish(5)
        }
    }

    @Test
    fun testWithTimeout() = runTest {
        withContext(SetTimeoutDispatcher) {
            val result = withTimeoutOrNull(10) {
                expect(1)
                delay(100)
                expectUnreached()
                42
            }
            assertNull(result)
            finish(2)
        }
    }
}
