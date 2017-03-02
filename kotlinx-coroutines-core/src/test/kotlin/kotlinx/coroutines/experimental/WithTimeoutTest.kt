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

import org.junit.Test

class WithTimeoutTest : TestBase() {
    /**
     * Tests property dispatching of `withTimeout` blocks
     */
    @Test
    fun testDispatch() = runBlocking {
        expect(1)
        launch(context) {
            expect(4)
            yield() // back to main
            expect(7)
        }
        expect(2)
        // test that it does not yield to the above job when started
        withTimeout(1000) {
            expect(3)
            yield() // yield only now
            expect(5)
        }
        expect(6)
        yield() // back to launch
        finish(8)
    }

    /**
     * Tests that a 100% CPU-consuming loop will react on timeout if it has yields.
     */
    @Test(expected = CancellationException::class)
    fun testYieldBlockingWithTimeout() = runBlocking {
        withTimeout(100) {
            while (true) {
                yield()
            }
        }
    }
}