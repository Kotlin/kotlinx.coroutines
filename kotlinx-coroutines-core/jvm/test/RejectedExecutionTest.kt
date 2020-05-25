/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.flow.*
import kotlinx.coroutines.scheduling.*
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
            assertIoThread() // was rejected on start, but start was atomic
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
                    assertExecutorThread()
                    try {
                        withContext(Dispatchers.Default) {
                            expect(3)
                            assertDefaultDispatcherThread()
                            // We have to wait until caller executor thread had already suspended (if not running task),
                            // so that we resume back to it a new task is posted
                            executor.awaitNotRunningTask()
                            expect(4)
                            assertDefaultDispatcherThread()
                        }
                        // cancelled on resume back
                    } finally {
                        expect(5)
                        assertIoThread()
                    }
                    expectUnreached()
                }
        }
        assertEquals(2, executor.submittedTasks)
        finish(6)
    }

    @Test
    fun testRejectOnDelay() = runTest {
        expect(1)
        executor.acceptTasks = 1 // accept one task
        assertFailsWith<CancellationException> {
            withContext(executor.asCoroutineDispatcher()) {
                expect(2)
                assertExecutorThread()
                try {
                    delay(10) // cancelled
                } finally {
                    // Since it was cancelled on attempt to delay, it still stays on the same thread
                    assertExecutorThread()
                }
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
                assertExecutorThread()
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
        val runningTask = MutableStateFlow(false)

        override fun schedule(command: Runnable, delay: Long, unit: TimeUnit): ScheduledFuture<*> {
            submittedTasks++
            if (submittedTasks > acceptTasks) throw RejectedExecutionException()
            val wrapper = Runnable {
                runningTask.value = true
                try {
                    command.run()
                } finally {
                    runningTask.value = false
                }
            }
            return super.schedule(wrapper, delay, unit)
        }

        suspend fun awaitNotRunningTask() = runningTask.first { !it }
    }

    private fun assertExecutorThread() {
        val thread = Thread.currentThread()
        if (!thread.name.startsWith(threadName)) error("Not an executor thread: $thread")
    }

    private fun assertDefaultDispatcherThread() {
        val thread = Thread.currentThread()
        if (thread !is CoroutineScheduler.Worker) error("Not a thread from Dispatchers.Default: $thread")
        assertEquals(CoroutineScheduler.WorkerState.CPU_ACQUIRED, thread.state)
    }

    private fun assertIoThread() {
        val thread = Thread.currentThread()
        if (thread !is CoroutineScheduler.Worker) error("Not a thread from Dispatchers.IO: $thread")
        assertEquals(CoroutineScheduler.WorkerState.BLOCKING, thread.state)
    }
}