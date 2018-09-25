/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import org.junit.*

class AwaitJvmTest : TestBase() {
    @Test
    public fun testSecondLeak() = runTest {
        // This test is to make sure that handlers installed on the second deferred do not leak
        val d1 = CompletableDeferred<Int>()
        val d2 = CompletableDeferred<Int>()
        d1.cancel(TestException()) // first is crashed
        val iterations = 3_000_000 * stressTestMultiplier
        for (iter in 1..iterations) {
            try {
                awaitAll(d1, d2)
                expectUnreached()
            } catch (e: TestException) {
                expect(iter)
            }
        }
        finish(iterations + 1)
    }

    private class TestException : Exception()
}