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

class AbstractCoroutineTest : TestBase() {
    @Test
    fun testNotifications() = runTest {
        expect(1)
        val coroutine = object : AbstractCoroutine<String>(coroutineContext, false) {
            override fun onStart() {
                expect(3)
            }

            override fun onCancellation(cause: Throwable?) {
                assertTrue(cause == null)
                expect(5)
            }

            override fun onCompleted(value: String) {
                assertEquals("OK", value)
                expect(6)
            }

            override fun onCompletedExceptionally(exception: Throwable) {
                expectUnreached()
            }
        }
        coroutine.invokeOnCompletion {
            assertTrue(it == null)
            expect(7)
        }
        expect(2)
        coroutine.start()
        expect(4)
        coroutine.resume("OK")
        finish(8)
    }

    @Test
    fun testNotificationsWithException() = runTest {
        expect(1)
        val coroutine = object : AbstractCoroutine<String>(coroutineContext, false) {
            override fun onStart() {
                expect(3)
            }

            override fun onCancellation(cause: Throwable?) {
                assertTrue(cause is TestException0)
                expect(5)
            }

            override fun onCompleted(value: String) {
                expectUnreached()
            }

            override fun onCompletedExceptionally(exception: Throwable) {
                assertTrue(exception is TestException1)
                expect(7)
            }
        }
        coroutine.invokeOnCompletion {
            assertTrue(it is TestException1)
            expect(8)
        }
        expect(2)
        coroutine.start()
        expect(4)
        coroutine.cancel(TestException0())
        expect(6)
        coroutine.resumeWithException(TestException1())
        finish(9)
    }

    private class TestException0 : Throwable()
    private class TestException1 : Throwable()
}