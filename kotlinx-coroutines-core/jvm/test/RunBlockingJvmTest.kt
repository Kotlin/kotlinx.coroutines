package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import java.util.concurrent.CountDownLatch
import kotlin.concurrent.thread
import kotlin.test.*
import kotlin.time.Duration

class RunBlockingJvmTest : TestBase() {
    @Test
    fun testContract() {
        val rb: Int
        runBlocking {
            rb = 42
        }
        rb.hashCode() // unused
    }

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

    private fun startInSeparateThreadAndInterrupt(action: (mayInterrupt: () -> Unit) -> Unit) {
        val latch = CountDownLatch(1)
        val thread = thread {
            action { latch.countDown() }
        }
        latch.await()
        thread.interrupt()
        thread.join()
    }
}
