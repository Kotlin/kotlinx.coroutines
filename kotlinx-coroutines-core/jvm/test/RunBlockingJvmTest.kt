package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import java.util.concurrent.CountDownLatch
import java.util.concurrent.atomic.AtomicReference
import kotlin.concurrent.thread
import kotlin.test.*
import kotlin.time.Duration

class RunBlockingJvmTest : TestBase() {

    /** Tests that the [runBlocking] coroutine runs to completion even it was interrupted. */
    @Test
    fun testFinishingWhenInterrupted() {
        startInSeparateThreadAndInterrupt { mayInterrupt ->
            expect(1)
            try {
                runBlocking {
                    try {
                        mayInterrupt()
                        expect(2)
                        delay(Duration.INFINITE)
                    } finally {
                        withContext(NonCancellable) {
                            expect(3)
                            repeat(10) { yield() }
                            expect(4)
                        }
                    }
                }
            } catch (_: InterruptedException) {
                expect(5)
            }
        }
        finish(6)
    }

    /** Tests that [runBlocking] will exit if it gets interrupted. */
    @Test
    fun testCancellingWhenInterrupted() {
        startInSeparateThreadAndInterrupt { mayInterrupt ->
            expect(1)
            try {
                runBlocking {
                    try {
                        mayInterrupt()
                        expect(2)
                        delay(Duration.INFINITE)
                    } catch (_: CancellationException) {
                        expect(3)
                    }
                }
            } catch (_: InterruptedException) {
                expect(4)
            }
        }
        finish(5)
    }

    /** Tests that [runBlocking] does not check for interruptions before the first attempt to suspend,
     * as no blocking actually happens. */
    @Test
    fun testInitialPortionRunningDespiteInterruptions() {
        Thread.currentThread().interrupt()
        runBlocking {
            expect(1)
            try {
                Thread.sleep(Long.MAX_VALUE)
            } catch (_: InterruptedException) {
                expect(2)
            }
        }
        assertFalse(Thread.interrupted())
        finish(3)
    }

    /**
     * Tests that [runBlockingNonInterruptible] is going to run its job to completion even if it gets interrupted
     * or if thread switches occur.
     */
    @Test
    fun testNonInterruptibleRunBlocking() {
        startInSeparateThreadAndInterrupt { mayInterrupt ->
            val v = runBlockingNonInterruptible {
                mayInterrupt()
                repeat(10) {
                    expect(it + 1)
                    delay(1)
                }
                42
            }
            assertTrue(Thread.interrupted())
            assertEquals(42, v)
            expect(11)
        }
        finish(12)
    }

    /**
     * Tests that [runBlockingNonInterruptible] is going to run its job to completion even if it gets interrupted
     * or if thread switches occur, and then will rethrow the exception thrown by the job.
     */
    @Test
    fun testNonInterruptibleRunBlockingFailure() {
        val exception = AssertionError()
        startInSeparateThreadAndInterrupt { mayInterrupt ->
            val exception2 = assertFailsWith<AssertionError> {
                runBlockingNonInterruptible {
                    mayInterrupt()
                    repeat(10) {
                        expect(it + 1)
                        // even thread switches should not be a problem
                        withContext(Dispatchers.IO) {
                            delay(1)
                        }
                    }
                    throw exception
                }
            }
            assertTrue(Thread.interrupted())
            assertSame(exception, exception2)
            expect(11)
        }
        finish(12)
    }


    /**
     * Tests that [runBlockingNonInterruptible] is going to run its job to completion even if it gets interrupted
     * or if thread switches occur.
     */
    @Test
    fun testNonInterruptibleRunBlockingPropagatingInterruptions() {
        val exception = AssertionError()
        startInSeparateThreadAndInterrupt { mayInterrupt ->
            runBlockingNonInterruptible {
                mayInterrupt()
                try {
                    Thread.sleep(Long.MAX_VALUE)
                } catch (_: InterruptedException) {
                    expect(1)
                }
            }
            expect(2)
            assertFalse(Thread.interrupted())
        }
        finish(3)
    }

    /**
     * Tests that starting [runBlockingNonInterruptible] in an interrupted thread does not affect the result.
     */
    @Test
    fun testNonInterruptibleRunBlockingStartingInterrupted() {
        Thread.currentThread().interrupt()
        val v = runBlockingNonInterruptible { 42 }
        assertEquals(42, v)
        assertTrue(Thread.interrupted())
    }

    private fun startInSeparateThreadAndInterrupt(action: (mayInterrupt: () -> Unit) -> Unit) {
        val latch = CountDownLatch(1)
        val thread = thread {
            action { latch.countDown() }
        }
        latch.await()
        thread.interrupt()
        thread.join()
    }

    private fun <T> runBlockingNonInterruptible(action: suspend () -> T): T {
        val result = AtomicReference<Result<T>>()
        try {
            runBlocking {
                withContext(NonCancellable) {
                    result.set(runCatching { action() })
                }
            }
        } catch (_: InterruptedException) {
            Thread.currentThread().interrupt() // restore the interrupted flag
        }
        return result.get().getOrThrow()
    }
}

internal actual fun runningOnIoThread(): Boolean = Thread.currentThread().isIoDispatcherThread()
