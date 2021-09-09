/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class CompletableJobTest : TestBase() {
    @Test
    fun testComplete() {
        val job = Job()
        assertTrue(job.isActive)
        assertFalse(job.isCompleted)
        assertTrue(job.complete())
        assertTrue(job.isCompleted)
        assertFalse(job.isActive)
        assertFalse(job.isCancelled)
        assertFalse(job.complete())
    }

    @Test
    fun testCompleteWithException() {
        val job = Job()
        assertTrue(job.isActive)
        assertFalse(job.isCompleted)
        assertTrue(job.completeExceptionally(TestException()))
        assertTrue(job.isCompleted)
        assertFalse(job.isActive)
        assertTrue(job.isCancelled)
        assertFalse(job.completeExceptionally(TestException()))
        assertFalse(job.complete())
    }

    @Test
    fun testCompleteWithChildren() {
        val parent = Job()
        val child = Job(parent)
        assertTrue(parent.complete())
        assertFalse(parent.complete())
        assertTrue(parent.isActive)
        assertFalse(parent.isCompleted)
        assertTrue(child.complete())
        assertTrue(child.isCompleted)
        assertTrue(parent.isCompleted)
        assertFalse(child.isActive)
        assertFalse(parent.isActive)
    }

    @Test
    fun testExceptionIsNotReportedToChildren() = parametrized { job ->
        expect(1)
        val child = launch(job) {
            expect(2)
            try {
                // KT-33840
                hang {}
            } catch (e: Throwable) {
                assertTrue(e is CancellationException)
                assertTrue((if (RECOVER_STACK_TRACES) e.cause?.cause else e.cause) is TestException)
                expect(4)
                throw e
            }
        }
        yield()
        expect(3)
        job.completeExceptionally(TestException())
        child.join()
        finish(5)
    }

    @Test
    fun testCompleteExceptionallyDoesntAffectDeferred() = parametrized { job ->
        expect(1)
        val child = async(job) {
            expect(2)
            try {
                // KT-33840
                hang {}
            } catch (e: Throwable) {
                assertTrue(e is CancellationException)
                assertTrue((if (RECOVER_STACK_TRACES) e.cause?.cause else e.cause) is TestException)
                expect(4)
                throw e
            }
        }
        yield()
        expect(3)
        job.completeExceptionally(TestException())
        child.join()
        assertTrue { child.getCompletionExceptionOrNull() is CancellationException }
        finish(5)
    }

    private fun parametrized(block: suspend CoroutineScope.(CompletableJob) -> Unit) {
        runTest {
            block(Job())
            reset()
            block(SupervisorJob())
        }
    }
}
