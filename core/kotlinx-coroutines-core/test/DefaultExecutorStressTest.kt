/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import org.junit.*

class DefaultExecutorStressTest : TestBase() {
    @Test
    fun testDelay() = runTest {
        val iterations = 100_000 * stressTestMultiplier
        withContext(DefaultExecutor) {
            expect(1)
            var expected = 1
            repeat(iterations) {
                expect(++expected)
                val deferred = async {
                    expect(++expected)
                    val largeArray = IntArray(10_000) { it }
                    delay(Long.MAX_VALUE)
                    println(largeArray) // consume to avoid DCE, actually unreachable
                }

                expect(++expected)
                yield()
                deferred.cancel()
                try {
                    deferred.await()
                } catch (e: CancellationException) {
                    expect(++expected)
                }
            }

        }
        finish(2 + iterations * 4)
    }
}
