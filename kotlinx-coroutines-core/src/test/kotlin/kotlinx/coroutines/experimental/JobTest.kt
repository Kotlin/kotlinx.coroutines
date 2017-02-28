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

import org.junit.Assert.assertEquals
import org.junit.Test

class JobTest : TestBase() {
    @Test
    fun testState() {
        val job = Job()
        check(job.isActive)
        job.cancel()
        check(!job.isActive)
    }

    @Test
    fun testHandler() {
        val job = Job()
        var fireCount = 0
        job.invokeOnCompletion { fireCount++ }
        check(job.isActive)
        assertEquals(0, fireCount)
        // cancel once
        job.cancel()
        check(!job.isActive)
        assertEquals(1, fireCount)
        // cancel again
        job.cancel()
        check(!job.isActive)
        assertEquals(1, fireCount)
    }

    @Test
    fun testManyHandlers() {
        val job = Job()
        val n = 100 * stressTestMultiplier
        val fireCount = IntArray(n)
        for (i in 0 until n) job.invokeOnCompletion { fireCount[i]++ }
        check(job.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        // cancel once
        job.cancel()
        check(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        // cancel again
        job.cancel()
        check(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
    }

    @Test
    fun testUnregisterInHandler() {
        val job = Job()
        val n = 100 * stressTestMultiplier
        val fireCount = IntArray(n)
        for (i in 0 until n) {
            var registration: Job.Registration? = null
            registration = job.invokeOnCompletion {
                fireCount[i]++
                registration!!.unregister()
            }
        }
        check(job.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        // cancel once
        job.cancel()
        check(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        // cancel again
        job.cancel()
        check(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
    }

    @Test
    fun testManyHandlersWithUnregister() {
        val job = Job()
        val n = 100 * stressTestMultiplier
        val fireCount = IntArray(n)
        val registrations = Array<Job.Registration>(n) { i -> job.invokeOnCompletion { fireCount[i]++ } }
        check(job.isActive)
        fun unreg(i: Int) = i % 4 <= 1
        for (i in 0 until n) if (unreg(i)) registrations[i].unregister()
        for (i in 0 until n) assertEquals(0, fireCount[i])
        job.cancel()
        check(!job.isActive)
        for (i in 0 until n) assertEquals(if (unreg(i)) 0 else 1, fireCount[i])
    }

    @Test
    fun testExceptionsInHandler() {
        val job = Job()
        val n = 100 * stressTestMultiplier
        val fireCount = IntArray(n)
        class TestException : Throwable()
        for (i in 0 until n) job.invokeOnCompletion {
            fireCount[i]++
            throw TestException()
        }
        check(job.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        val tryCancel = Try<Unit> { job.cancel() }
        check(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        check(tryCancel.exception is TestException)
    }

    @Test
    fun testMemoryRelease() {
        val job = Job()
        val n = 10_000_000 * stressTestMultiplier
        var fireCount = 0
        for (i in 0 until n) job.invokeOnCompletion { fireCount++ }.unregister()
    }
    
    @Test
    fun testCancelledParent() {
        val parent = Job()
        parent.cancel()
        check(!parent.isActive)
        val child = Job(parent)
        check(!child.isActive)
    }
}