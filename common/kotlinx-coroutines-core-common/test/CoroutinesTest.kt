/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlin.test.*

class CoroutinesTest : TestBase() {

    @Test
    fun testSimple() = runTest {
        expect(1)
        finish(2)
    }

    @Test
    fun testYield() = runTest {
        expect(1)
        yield() // effectively does nothing, as we don't have other coroutines
        finish(2)
    }

    @Test
    fun testLaunchAndYieldJoin() = runTest {
        expect(1)
        val job = launch {
            expect(3)
            yield()
            expect(4)
        }
        expect(2)
        assertTrue(job.isActive && !job.isCompleted)
        job.join()
        assertTrue(!job.isActive && job.isCompleted)
        finish(5)
    }

    @Test
    fun testLaunchUndispatched() = runTest {
        expect(1)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            yield()
            expect(4)
        }
        expect(3)
        assertTrue(job.isActive && !job.isCompleted)
        job.join()
        assertTrue(!job.isActive && job.isCompleted)
        finish(5)
    }

    @Test
    fun testNested() = runTest {
        expect(1)
        val j1 = launch {
            expect(3)
            val j2 = launch {
                expect(5)
            }
            expect(4)
            j2.join()
            expect(6)
        }
        expect(2)
        j1.join()
        finish(7)
    }

    @Test
    fun testWaitChild() = runTest {
        expect(1)
        launch {
            expect(3)
            yield() // to parent
            finish(5)
        }
        expect(2)
        yield()
        expect(4)
        // parent waits for child's completion
    }

    @Test
    fun testCancelChildExplicit() = runTest {
        expect(1)
        val job = launch {
            expect(3)
            yield()
            expectUnreached()
        }
        expect(2)
        yield()
        expect(4)
        job.cancel()
        finish(5)
    }

    @Test
    fun testCancelChildWithFinally() = runTest {
        expect(1)
        val job = launch {
            expect(3)
            try {
                yield()
            } finally {
                finish(6) // cancelled child will still execute finally
            }
            expectUnreached()
        }
        expect(2)
        yield()
        expect(4)
        job.cancel()
        expect(5)
    }

    @Test
    fun testWaitNestedChild() = runTest {
        expect(1)
        launch {
            expect(3)
            launch {
                expect(6)
                yield() // to parent
                expect(9)
            }
            expect(4)
            yield()
            expect(7)
            yield()  // to parent
            finish(10) // the last one to complete
        }
        expect(2)
        yield()
        expect(5)
        yield()
        expect(8)
        // parent waits for child
    }

    @Test
    fun testExceptionPropagation() = runTest(
        expected = { it is TestException }
    ) {
        finish(1)
        throw TestException()
    }

    @Test
    fun testCancelParentOnChildException() = runTest(expected = { it is TestException }) {
        expect(1)
        launch {
            finish(3)
            throwTestException() // does not propagate exception to launch, but cancels parent (!)
            expectUnreached()
        }
        expect(2)
        yield()
        expectUnreached() // because of exception in child
    }

    @Test
    fun testCancelParentOnNestedException() = runTest(expected = { it is TestException }) {
        expect(1)
        launch {
            expect(3)
            launch {
                finish(6)
                throwTestException() // unhandled exception kills all parents
                expectUnreached()
            }
            expect(4)
            yield()
            expectUnreached() // because of exception in child
        }
        expect(2)
        yield()
        expect(5)
        yield()
        expectUnreached() // because of exception in child
    }

    @Test
    fun testJoinWithFinally() = runTest {
        expect(1)
        val job = launch {
            expect(3)
            try {
                yield() // to main, will cancel us
            } finally {
                expect(7) // join is waiting
            }
        }
        expect(2)
        yield() // to job
        expect(4)
        assertTrue(job.isActive && !job.isCompleted)
        assertTrue(job.cancel())  // cancels job
        expect(5) // still here
        assertTrue(!job.isActive && !job.isCompleted)
        assertTrue(job.cancel()) // second attempt returns true as well, job is still completing
        expect(6) // we're still here
        job.join() // join the job, let job complete its "finally" section
        expect(8)
        assertTrue(!job.isActive && job.isCompleted)
        finish(9)
    }

    @Test
    fun testCancelAndJoin() = runTest {
        expect(1)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            try {
                expect(2)
                yield()
                expectUnreached() // will get cancelled
            } finally {
                expect(4)
            }
        }
        expect(3)
        job.cancelAndJoin()
        finish(5)
    }

    @Test
    fun testCancelAndJoinChildCrash() = runTest(expected = { it is TestException }) {
        expect(1)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            throwTestException()
            expectUnreached()
        }
        // now we have a failed job with TestException
        finish(3)
        try {
            job.cancelAndJoin() // join should crash on child's exception but it will be wrapped into CancellationException
        } catch (e: Throwable) {
            e as CancellationException // type assertion
            assertTrue(e.cause is TestException)
            throw e
        }
        expectUnreached()
    }

    @Test
    fun testYieldInFinally() = runTest(
        expected = { it is TestException }
    ) {
        expect(1)
        try {
            expect(2)
            throwTestException()
        } finally {
            expect(3)
            yield()
            finish(4)
        }
        expectUnreached()
    }

    @Test
    fun testCancelAndJoinChildren() = runTest {
        expect(1)
        val parent = Job()
        launch(parent, CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                yield() // to be cancelled
            } finally {
                expect(5)
            }
            expectUnreached()
        }
        expect(3)
        parent.cancelChildren()
        expect(4)
        parent.children.forEach { it.join() } // will yield to child
        assertTrue(parent.isActive) // make sure it did not cancel parent
        finish(6)
    }

    @Test
    fun testParentCrashCancelsChildren() = runTest(
        unhandled = listOf({ it -> it is TestException })
    ) {
        expect(1)
        val parent = launch(Job()) {
            expect(4)
            throw TestException("Crashed")
        }
        launch(parent, CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                yield() // to test
            } finally {
                expect(5)
                withContext(NonCancellable) { yield() } // to test
                expect(7)
            }
            expectUnreached() // will get cancelled, because parent crashes
        }
        expect(3)
        yield() // to parent
        expect(6)
        parent.join() // make sure crashed parent still waits for its child
        finish(8)
    }

    @Test
    fun testNotCancellableChildWithExceptionCancelled() = runTest(expected = { it is IllegalArgumentException }) {
        expect(1)
        // CoroutineStart.ATOMIC makes sure it will not get cancelled for it starts executing
        val d = async(start = CoroutineStart.ATOMIC) {
            finish(4)
            throwTestException() // will throw
            expectUnreached()
        }
        expect(2)
        // now cancel with some other exception
        d.cancel(IllegalArgumentException())
        // now await to see how it got crashed -- IAE should have been suppressed by TestException
        expect(3)
        d.await()
    }

    private fun throwTestException() { throw TestException() }

    private class TestException : Exception {
        constructor(message: String): super(message)
        constructor(): super()
    }
}