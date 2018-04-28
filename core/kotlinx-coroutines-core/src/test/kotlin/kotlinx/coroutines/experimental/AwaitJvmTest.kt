/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import org.junit.*

class AwaitJvmTest : TestBase() {
    @Test
    public fun testSecondLeak() = runTest {
        // This test is to make sure that handlers installed on the second deferred do not leak
        val d1 = CompletableDeferred<Int>()
        val d2 = CompletableDeferred<Int>()
        d1.completeExceptionally(TestException()) // first is crashed
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