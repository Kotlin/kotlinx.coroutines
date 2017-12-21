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

import kotlin.test.*

class CoroutinesTest : TestBase() {
    @Test
    fun testNotCancellableCodeWithExceptionCancelled() = runTest {
        expect(1)
        // CoroutineStart.ATOMIC makes sure it will not get cancelled for it starts executing
        val job = launch(start = CoroutineStart.ATOMIC) {
            Thread.sleep(100) // cannot be cancelled
            throwTestException() // will throw
            expectUnreached()
        }
        expect(2)
        job.cancel()
        finish(3)
    }

    @Test
    fun testCancelManyCompletedAttachedChildren() = runTest {
        val parent = launch(coroutineContext) { /* do nothing */ }
        val n = 10_000 * stressTestMultiplier
        repeat(n) {
            // create a child that already completed
            val child = launch(coroutineContext, CoroutineStart.UNDISPATCHED) { /* do nothing */ }
            // attach it manually
            parent.attachChild(child)
        }
        parent.cancelAndJoin() // cancel parent, make sure no stack overflow
    }

    private fun throwTestException(): Unit = throw TestException()

    private class TestException() : Exception()
}