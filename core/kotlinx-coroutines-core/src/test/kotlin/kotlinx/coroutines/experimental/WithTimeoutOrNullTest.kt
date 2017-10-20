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

import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsNull
import org.junit.Assert.assertThat
import org.junit.Test
import java.io.IOException

class WithTimeoutOrNullTest : TestBase() {
    /**
     * Tests a case of no timeout and no suspension inside.
     */
    @Test
    fun testBasicNoSuspend() = runTest {
        expect(1)
        val result = withTimeoutOrNull(10_000) {
            expect(2)
            "OK"
        }
        assertThat(result, IsEqual("OK"))
        finish(3)
    }

    /**
     * Tests a case of no timeout and one suspension inside.
     */
    @Test
    fun testBasicSuspend() = runTest {
        expect(1)
        val result = withTimeoutOrNull(10_000) {
            expect(2)
            yield()
            expect(3)
            "OK"
        }
        assertThat(result, IsEqual("OK"))
        finish(4)
    }

    /**
     * Tests property dispatching of `withTimeoutOrNull` blocks
     */
    @Test
    fun testDispatch() = runTest {
        expect(1)
        launch(coroutineContext) {
            expect(4)
            yield() // back to main
            expect(7)
        }
        expect(2)
        // test that it does not yield to the above job when started
        val result = withTimeoutOrNull(1000) {
            expect(3)
            yield() // yield only now
            expect(5)
            "OK"
        }
        assertThat(result, IsEqual("OK"))
        expect(6)
        yield() // back to launch
        finish(8)
    }

    @Test
    fun testNullOnTimeout() = runTest {
        expect(1)
        val result = withTimeoutOrNull(100) {
            expect(2)
            delay(1000)
            expectUnreached()
            "OK"
        }
        assertThat(result, IsNull())
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
        assertThat(result, IsNull())
        finish(4)
    }

    @Test
    fun testSuppressExceptionWithAnotherException() = runTest(
        expected = { it is IOException }
    ) {
        expect(1)
        val result = withTimeoutOrNull(100) {
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

    /**
     * Tests that a 100% CPU-consuming loop will react on timeout if it has yields.
     */
    @Test
    fun testYieldBlockingWithTimeout() = runBlocking {
        expect(1)
        val result = withTimeoutOrNull(100) {
            while (true) {
                yield()
            }
        }
        assertThat(result, IsNull())
        finish(2)
    }

    @Test(expected = CancellationException::class)
    fun testInnerTimeoutTest() = runBlocking {
        withTimeoutOrNull(200) {
            withTimeout(100) {
                while (true) {
                    yield()
                }
            }
            expectUnreached() // will timeout
        }
        expectUnreached() // will timeout
    }

    @Test
    fun testOuterTimeoutTest() = runBlocking {
        var counter = 0
        val result = withTimeoutOrNull(250) {
            while (true) {
                val inner = withTimeoutOrNull(100) {
                    while (true) {
                        yield()
                    }
                }
                assertThat(inner, IsNull())
                counter++
            }
        }
        assertThat(result, IsNull())
        // under load counter may be equal to 1, so the check is lenient here
        println("Executed: $counter times")
        check(counter in 1..2)
    }

    @Test
    fun testOuterTimeoutFiredBeforeInner() = runBlocking<Unit> {
        val result = withTimeoutOrNull(100) {
            Thread.sleep(200) // wait enough for outer timeout to fire
            run(NonCancellable) { yield() } // give an event loop a chance to run and process that cancellation
            withTimeoutOrNull(100) {
                yield() // will cancel because of outer timeout
                expectUnreached()
            }
            expectUnreached() // should not be reached, because it is outer timeout
        }
        // outer timeout results in null
        assertThat(result, IsNull())
    }
}