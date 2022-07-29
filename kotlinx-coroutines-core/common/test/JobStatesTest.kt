/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines

import kotlin.test.*

/**
 * Tests that the transitions to the state of the [Job] correspond to documentation in the
 * table that is presented in the [Job] documentation.
 */
class JobStatesTest : TestBase() {
    @Test
    public fun testNormalCompletion() = runTest {
        expect(1)
        val parent = coroutineContext.job
        val job = launch(start = CoroutineStart.LAZY) {
            expect(2)
            // launches child
            launch {
                expect(4)
            }
            // completes normally
        }
        // New job
        assertFalse(job.isActive)
        assertFalse(job.isCompleted)
        assertFalse(job.isCancelled)
        assertSame(parent, job.parent)
        // New -> Active
        job.start()
        assertTrue(job.isActive)
        assertFalse(job.isCompleted)
        assertFalse(job.isCancelled)
        assertSame(parent, job.parent)
        // Active -> Completing
        yield() // scheduled & starts child
        expect(3)
        assertTrue(job.isActive)
        assertFalse(job.isCompleted)
        assertFalse(job.isCancelled)
        assertSame(parent, job.parent)
        // Completing -> Completed
        yield()
        finish(5)
        assertFalse(job.isActive)
        assertTrue(job.isCompleted)
        assertFalse(job.isCancelled)
        assertNull(job.parent)
    }

    @Test
    public fun testCompletingFailed() = runTest(
        unhandled = listOf({ it -> it is TestException })
    ) {
        expect(1)
        val job = launch(NonCancellable, start = CoroutineStart.LAZY) {
            expect(2)
            // launches child
            launch {
                expect(4)
                throw TestException()
            }
            // completes normally
        }
        // New job
        assertFalse(job.isActive)
        assertFalse(job.isCompleted)
        assertFalse(job.isCancelled)
        // New -> Active
        job.start()
        assertTrue(job.isActive)
        assertFalse(job.isCompleted)
        assertFalse(job.isCancelled)
        // Active -> Completing
        yield() // scheduled & starts child
        expect(3)
        assertTrue(job.isActive)
        assertFalse(job.isCompleted)
        assertFalse(job.isCancelled)
        // Completing -> Cancelled
        yield()
        finish(5)
        assertFalse(job.isActive)
        assertTrue(job.isCompleted)
        assertTrue(job.isCancelled)
    }

    @Test
    public fun testFailed() = runTest(
        unhandled = listOf({ it -> it is TestException })
    ) {
        expect(1)
        val job = launch(NonCancellable, start = CoroutineStart.LAZY) {
            expect(2)
            // launches child
            launch(start = CoroutineStart.ATOMIC) {
                expect(4)
            }
            // failing
            throw TestException()
        }
        // New job
        assertFalse(job.isActive)
        assertFalse(job.isCompleted)
        assertFalse(job.isCancelled)
        // New -> Active
        job.start()
        assertTrue(job.isActive)
        assertFalse(job.isCompleted)
        assertFalse(job.isCancelled)
        // Active -> Cancelling
        yield() // scheduled & starts child
        expect(3)
        assertFalse(job.isActive)
        assertFalse(job.isCompleted)
        assertTrue(job.isCancelled)
        // Cancelling -> Cancelled
        yield()
        finish(5)
        assertFalse(job.isActive)
        assertTrue(job.isCompleted)
        assertTrue(job.isCancelled)
    }

    @Test
    public fun testCancelling() = runTest {
        expect(1)
        val job = launch(NonCancellable, start = CoroutineStart.LAZY) {
            expect(2)
            // launches child
            launch(start = CoroutineStart.ATOMIC) {
                expect(4)
            }
            // completes normally
        }
        // New job
        assertFalse(job.isActive)
        assertFalse(job.isCompleted)
        assertFalse(job.isCancelled)
        // New -> Active
        job.start()
        assertTrue(job.isActive)
        assertFalse(job.isCompleted)
        assertFalse(job.isCancelled)
        // Active -> Completing
        yield() // scheduled & starts child
        expect(3)
        assertTrue(job.isActive)
        assertFalse(job.isCompleted)
        assertFalse(job.isCancelled)
        // Completing -> Cancelling
        job.cancel()
        assertFalse(job.isActive)
        assertFalse(job.isCompleted)
        assertTrue(job.isCancelled)
        // Cancelling -> Cancelled
        yield()
        finish(5)
        assertFalse(job.isActive)
        assertTrue(job.isCompleted)
        assertTrue(job.isCancelled)
    }
}
