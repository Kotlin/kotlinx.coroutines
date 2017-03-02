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

class LaunchLazyTest : TestBase() {
    @Test
    fun testLaunchAndYieldJoin() = runBlocking {
        expect(1)
        val job = launch(context, start = false) {
            expect(4)
            yield() // does nothing -- main waits
            expect(5)
        }
        expect(2)
        yield() // does nothing, was not started yet
        expect(3)
        check(!job.isActive && !job.isCompleted)
        job.join()
        check(!job.isActive && job.isCompleted)
        finish(6)
    }

    @Test
    fun testStart() = runBlocking {
        expect(1)
        val job = launch(context, start = false) {
            expect(5)
            yield() // yields back to main
            expect(7)
        }
        expect(2)
        yield() // does nothing, was not started yet
        expect(3)
        check(!job.isActive && !job.isCompleted)
        check(job.start())
        check(job.isActive && !job.isCompleted)
        check(!job.start()) // start again -- does nothing
        check(job.isActive && !job.isCompleted)
        expect(4)
        yield() // now yield to started coroutine
        expect(6)
        check(job.isActive && !job.isCompleted)
        yield() // yield again
        check(!job.isActive && job.isCompleted) // it completes this time
        expect(8)
        job.join() // immediately returns
        finish(9)
    }
}
