/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class RejectedExecutionTest : TestBase() {
    private val threadName = "RejectedExecutionTest"
    private val executor = RejectingExecutor()

    @After
    fun tearDown() {
        executor.shutdown()
        executor.awaitTermination(10, TimeUnit.SECONDS)
    }

    @Test
    fun testRejectOnLaunch() = runTest {
        expect(1)
        val job = launch(executor.asCoroutineDispatcher()) {
            expectUnreached()
        }
        assertEquals(1, executor.submittedTasks)
        assertTrue(job.isCancelled)
        finish(2)
    }

    @Test
    fun testRejectOnLaunchAtomic() = runTest {
        expect(1)
        val job = launch(executor.asCoroutineDispatcher(), start = CoroutineStart.ATOMIC) {
            expect(2)
            assertEquals(true, coroutineContext[Job]?.isCancelled)
            assertNotSame(threadName, Thread.currentThread().name) // should have got dispatched on the DefaultExecutor
        }
        assertEquals(1, executor.submittedTasks)
        job.join()
        finish(3)
    }

    @Test
    fun testRejectOnWithContext() = runTest {
        expect(1)
        assertFailsWith<CancellationException> {
            withContext(executor.asCoroutineDispatcher()) {
                expectUnreached()
            }
        }
        assertEquals(1, executor.submittedTasks)
        finish(2)
    }

    @Test
    fun testRejectOnResumeInContext() = runTest {
        expect(1)
        executor.acceptTasks = 1 // accept one task
        assertFailsWith<CancellationException> {
            withContext(executor.asCoroutineDispatcher()) {
                expect(2)
                withContext(Dispatchers.Default) {
                    expect(3)
                }
                // cancelled on resume back
                expectUnreached()
            }
        }
        assertEquals(2, executor.submittedTasks)
        finish(4)
    }

    @Test
    fun testRejectOnDelay() = runTest {
        expect(1)
        executor.acceptTasks = 1 // accept one task
        assertFailsWith<CancellationException> {
            withContext(executor.asCoroutineDispatcher()) {
                expect(2)
                delay(10) // cancelled
                expectUnreached()
            }
        }
        assertEquals(2, executor.submittedTasks)
        finish(3)
    }

    @Test
    fun testRejectWithTimeout() = runTest {
        expect(1)
        executor.acceptTasks = 1 // accept one task
        assertFailsWith<CancellationException> {
            withContext(executor.asCoroutineDispatcher()) {
                expect(2)
                withTimeout(1000) {
                    expect(3) // atomic entry into the block (legacy behavior, it seem to be Ok with way)
                    assertEquals(true, coroutineContext[Job]?.isCancelled) // but the job is already cancelled
                }
                expectUnreached()
            }
        }
        assertEquals(2, executor.submittedTasks)
        finish(4)
    }

    private inner class RejectingExecutor : ScheduledThreadPoolExecutor(1, { r -> Thread(r, threadName) }) {
        var acceptTasks = 0
        var submittedTasks = 0

        override fun schedule(command: Runnable, delay: Long, unit: TimeUnit): ScheduledFuture<*> {
            submittedTasks++
            if (submittedTasks > acceptTasks) throw RejectedExecutionException()
            return super.schedule(command, delay, unit)
        }
    }
}