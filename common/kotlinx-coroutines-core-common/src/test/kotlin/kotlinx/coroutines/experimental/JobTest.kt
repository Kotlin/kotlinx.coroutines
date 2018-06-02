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

class JobTest : TestBase() {
    @Test
    fun testState() {
        val job = Job()
        assertTrue(job.isActive)
        job.cancel()
        assertTrue(!job.isActive)
    }

    @Test
    fun testHandler() {
        val job = Job()
        var fireCount = 0
        job.invokeOnCompletion { fireCount++ }
        assertTrue(job.isActive)
        assertEquals(0, fireCount)
        // cancel once
        job.cancel()
        assertTrue(!job.isActive)
        assertEquals(1, fireCount)
        // cancel again
        job.cancel()
        assertTrue(!job.isActive)
        assertEquals(1, fireCount)
    }

    @Test
    fun testManyHandlers() {
        val job = Job()
        val n = 100 * stressTestMultiplier
        val fireCount = IntArray(n)
        for (i in 0 until n) job.invokeOnCompletion { fireCount[i]++ }
        assertTrue(job.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        // cancel once
        job.cancel()
        assertTrue(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        // cancel again
        job.cancel()
        assertTrue(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
    }

    @Test
    fun testUnregisterInHandler() {
        val job = Job()
        val n = 100 * stressTestMultiplier
        val fireCount = IntArray(n)
        for (i in 0 until n) {
            var registration: DisposableHandle? = null
            registration = job.invokeOnCompletion {
                fireCount[i]++
                registration!!.dispose()
            }
        }
        assertTrue(job.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        // cancel once
        job.cancel()
        assertTrue(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        // cancel again
        job.cancel()
        assertTrue(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
    }

    @Test
    fun testManyHandlersWithUnregister() {
        val job = Job()
        val n = 100 * stressTestMultiplier
        val fireCount = IntArray(n)
        val registrations = Array<DisposableHandle>(n) { i -> job.invokeOnCompletion { fireCount[i]++ } }
        assertTrue(job.isActive)
        fun unreg(i: Int) = i % 4 <= 1
        for (i in 0 until n) if (unreg(i)) registrations[i].dispose()
        for (i in 0 until n) assertEquals(0, fireCount[i])
        job.cancel()
        assertTrue(!job.isActive)
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
        assertTrue(job.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        val tryCancel = Try<Unit> { job.cancel() }
        assertTrue(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        assertTrue(tryCancel.exception is CompletionHandlerException)
        assertTrue(tryCancel.exception!!.cause is TestException)
    }

    @Test
    fun testCancelledParent() {
        val parent = Job()
        parent.cancel()
        assertTrue(!parent.isActive)
        val child = Job(parent)
        assertTrue(!child.isActive)
    }

    @Test
    fun testDisposeSingleHandler() {
        val job = Job()
        var fireCount = 0
        val handler = job.invokeOnCompletion { fireCount++ }
        handler.dispose()
        job.cancel()
        assertEquals(0, fireCount)
    }

    @Test
    fun testDisposeMultipleHandler() {
        val job = Job()
        val handlerCount = 10
        var fireCount = 0
        val handlers = Array(handlerCount) { job.invokeOnCompletion { fireCount++ } }
        handlers.forEach { it.dispose() }
        job.cancel()
        assertEquals(0, fireCount)
    }

    @Test
    fun testCancelAndJoinParentWaitChildren() = runTest {
        expect(1)
        val parent = Job()
        launch(coroutineContext, start = CoroutineStart.UNDISPATCHED, parent = parent) {
            expect(2)
            try {
                yield() // will get cancelled
            } finally {
                expect(5)
            }
        }
        expect(3)
        parent.cancel()
        expect(4)
        parent.join()
        finish(6)
    }
}