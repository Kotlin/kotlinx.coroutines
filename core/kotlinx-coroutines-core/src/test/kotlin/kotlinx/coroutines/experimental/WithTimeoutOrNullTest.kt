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

class WithTimeoutOrNullTest : TestBase() {
    @Test
    fun testNullOnTimeout() = runTest {
        expect(1)
        val result = withTimeoutOrNull(100) {
            expect(2)
            delay(1000)
            expectUnreached()
            "OK"
        }
        assertEquals(null, result)
        finish(3)
    }

    @Test
    fun testSuppressExceptionWithResult() = runTest {
        expect(1)
        val result = withTimeoutOrNull(100) {
            expect(2)
            try {
                delay(1000)
            } catch (e: CancellationException) {
                expect(3)
            }
            "OK"
        }
        assertEquals(null, result)
        finish(4)
    }

    @Test
    fun testSuppressExceptionWithAnotherException() = runTest(
        expected = { it is TestException }
    ) {
        expect(1)
        val result = withTimeoutOrNull(100) {
            expect(2)
            try {
                delay(1000)
            } catch (e: CancellationException) {
                finish(3)
                throw TestException()
            }
            expectUnreached()
            "OK"
        }
        expectUnreached()
    }

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

    private class TestException : Exception()
}