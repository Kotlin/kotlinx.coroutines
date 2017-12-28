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

class CommonLaunchLazyTest : TestBase() {
    @Test
    fun testLaunchAndYieldJoin() = runTest {
        expect(1)
        val job = launch(coroutineContext, CoroutineStart.LAZY) {
            expect(4)
            yield() // does nothing -- main waits
            expect(5)
        }
        expect(2)
        yield() // does nothing, was not started yet
        expect(3)
        assertTrue(!job.isActive && !job.isCompleted)
        job.join()
        assertTrue(!job.isActive && job.isCompleted)
        finish(6)
    }

    @Test
    fun testStart() = runTest {
        expect(1)
        val job = launch(coroutineContext, CoroutineStart.LAZY) {
            expect(5)
            yield() // yields back to main
            expect(7)
        }
        expect(2)
        yield() // does nothing, was not started yet
        expect(3)
        assertTrue(!job.isActive && !job.isCompleted)
        assertTrue(job.start())
        assertTrue(job.isActive && !job.isCompleted)
        assertTrue(!job.start()) // start again -- does nothing
        assertTrue(job.isActive && !job.isCompleted)
        expect(4)
        yield() // now yield to started coroutine
        expect(6)
        assertTrue(job.isActive && !job.isCompleted)
        yield() // yield again
        assertTrue(!job.isActive && job.isCompleted) // it completes this time
        expect(8)
        job.join() // immediately returns
        finish(9)
    }

    @Test
    fun testInvokeOnCompletionAndStart() = runTest {
        expect(1)
        val job = launch(coroutineContext, CoroutineStart.LAZY) {
            expect(5)
        }
        yield() // no started yet!
        expect(2)
        job.invokeOnCompletion {
            expect(6)
        }
        expect(3)
        job.start()
        expect(4)
        yield()
        finish(7)
    }
}
