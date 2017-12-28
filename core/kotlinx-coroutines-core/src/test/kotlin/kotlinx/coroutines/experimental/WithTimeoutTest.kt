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

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlin.test.*
import java.io.IOException

class WithTimeoutTest : TestBase() {
    @Test
    fun testExceptionOnTimeout() = runTest {
        expect(1)
        try {
            withTimeout(100) {
                expect(2)
                delay(1000)
                expectUnreached()
                "OK"
            }
        } catch (e: CancellationException) {
            assertEquals("Timed out waiting for 100 MILLISECONDS", e.message)
            finish(3)
        }
    }

    @Test
    fun testSuppressExceptionWithResult() = runTest(
        expected = { it is CancellationException }
    ) {
        expect(1)
        val result = withTimeout(100) {
            expect(2)
            try {
                delay(1000)
            } catch (e: CancellationException) {
                finish(3)
            }
            "OK"
        }
        expectUnreached()
    }

    @Test
    fun testSuppressExceptionWithAnotherException() = runTest(
        expected = { it is IOException }
    ) {
        expect(1)
        withTimeout(100) {
            expect(2)
            try {
                delay(1000)
            } catch (e: CancellationException) {
                finish(3)
                throw IOException(e)
            }
            expectUnreached()
            "OK"
        }
        expectUnreached()
    }
}