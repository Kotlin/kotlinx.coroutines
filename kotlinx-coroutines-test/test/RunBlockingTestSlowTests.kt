/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import org.junit.*
import org.junit.rules.*
import kotlin.concurrent.*

class RunBlockingTestSlowTests : TestBase() {
    /*
     * Tests that rely on time heavily
     */
    @get:Rule
    val timeout = Timeout.seconds(10)

    @Test
    fun testResumeFromAnotherThreadWithDelay() = runBlockingTest {
        expect(1)
        suspendCancellableCoroutine<Unit> { cont ->
            expect(2)
            thread {
                expect(3)
                Thread.sleep(100)
                cont.resume(Unit) { Unit }
            }
        }
        finish(4)
    }

    @Test(expected = UncompletedCoroutinesError::class)
    fun testSuspendForeverTimeout() = runBlockingTest(waitForOtherDispatchers = 100L) {
        suspendCancellableCoroutine<Unit> {  }
    }
}