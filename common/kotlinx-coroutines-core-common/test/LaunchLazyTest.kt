/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

class LaunchLazyTest : TestBase() {
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
