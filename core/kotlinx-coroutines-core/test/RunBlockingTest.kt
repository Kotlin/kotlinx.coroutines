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

import kotlin.coroutines.experimental.*
import kotlin.test.*

class RunBlockingTest : TestBase() {
    @Test
    fun testPrivateEventLoop() {
        expect(1)
        runBlocking {
            expect(2)
            assertTrue(coroutineContext[ContinuationInterceptor] is EventLoop)
            yield() // is supported!
            expect(3)
        }
        finish(4)
    }

    @Test
    fun testOuterEventLoop() {
        expect(1)
        runBlocking {
            expect(2)
            val outerEventLoop = coroutineContext[ContinuationInterceptor] as EventLoop
            runBlocking(coroutineContext) {
                expect(3)
                // still same event loop
                assertTrue(coroutineContext[ContinuationInterceptor] === outerEventLoop)
                yield() // still works
                expect(4)
            }
            expect(5)
        }
        finish(6)
    }

    @Test
    fun testOtherDispatcher() {
        expect(1)
        val name = "RunBlockingTest.testOtherDispatcher"
        val thread = newSingleThreadContext(name)
        runBlocking(thread) {
            expect(2)
            assertTrue(coroutineContext[ContinuationInterceptor] === thread)
            assertTrue(Thread.currentThread().name.contains(name))
            yield() // should work
            expect(3)
        }
        finish(4)
        thread.close()
    }
}