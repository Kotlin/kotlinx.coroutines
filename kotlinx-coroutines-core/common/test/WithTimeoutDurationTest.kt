package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*
import kotlin.time.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.seconds

class WithTimeoutDurationTest : TestBase() {
    /**
     * Tests a case of no timeout and no suspension inside.
     */
    @Test
    fun testBasicNoSuspend() = runTest {
        expect(1)
        val result = withTimeout(10.seconds) {
            expect(2)
            "OK"
        }
        assertEquals("OK", result)
        finish(3)
    }

    /**
     * Tests a case of no timeout and one suspension inside.
     */
    @Test
    fun testBasicSuspend() = runTest {
        expect(1)
        val result = withTimeout(10.seconds) {
            expect(2)
            yield()
            expect(3)
            "OK"
        }
        assertEquals("OK", result)
        finish(4)
    }

    /**
     * Tests proper dispatching of `withTimeout` blocks
     */
    @Test
    fun testDispatch() = runTest {
        expect(1)
        launch {
            expect(4)
            yield() // back to main
            expect(7)
        }
        expect(2)
        // test that it does not yield to the above job when started
        val result = withTimeout(1.seconds) {
            expect(3)
            yield() // yield only now
            expect(5)
            "OK"
        }
        assertEquals("OK", result)
        expect(6)
        yield() // back to launch
        finish(8)
    }


    /**
     * Tests that a 100% CPU-consuming loop will react on timeout if it has yields.
     */
    @Test
    fun testYieldBlockingWithTimeout() = runTest(
            expected = { it is CancellationException }
    ) {
        withTimeout(100.milliseconds) {
            while (true) {
                yield()
            }
        }
    }

    /**
     * Tests that [withTimeout] waits for children coroutines to complete.
     */
    @Test
    fun testWithTimeoutChildWait() = runTest {
        expect(1)
        withTimeout(100.milliseconds) {
            expect(2)
            // launch child with timeout
            launch {
                expect(4)
            }
            expect(3)
            // now will wait for child before returning
        }
        finish(5)
    }

    @Test
    fun testBadClass() = runTest {
        val bad = BadClass()
        val result = withTimeout(100.milliseconds) {
            bad
        }
        assertSame(bad, result)
    }

    class BadClass {
        override fun equals(other: Any?): Boolean = error("Should not be called")
        override fun hashCode(): Int = error("Should not be called")
        override fun toString(): String = error("Should not be called")
    }

    @Test
    fun testExceptionOnTimeout() = runTest {
        expect(1)
        val e = assertFailsWith<CancellationException> {
            withTimeout<String>(100.milliseconds) {
                expect(2)
                delay(1000.milliseconds)
                expectUnreached()
            }
        }
        assertEquals("Timed out waiting for 100 ms", e.message)
        finish(3)
    }

    @Test
    fun testSuppressExceptionWithResult() = runTest {
        expect(1)
        assertFailsWith<CancellationException> {
            withTimeout(100.milliseconds) {
                expect(2)
                assertFailsWith<CancellationException> {
                    delay(1000.milliseconds)
                }
                finish(3)
                "OK"
            }
        }
    }

    @Test
    fun testSuppressExceptionWithAnotherException() = runTest {
        expect(1)
        assertFailsWith<TestException> {
            withTimeout<String>(100.milliseconds) {
                expect(2)
                assertFailsWith<CancellationException> {
                    delay(1000.milliseconds)
                }
                expect(3)
                throw TestException()
            }
        }
        finish(4)
    }

    @Test
    fun testNegativeTimeout() = runTest {
        val e = assertFailsWith<TimeoutCancellationException> {
            withTimeout<String>((-1).milliseconds) {
                expectUnreached()
            }
        }
        assertEquals("Timed out immediately", e.message)
    }

    @Test
    fun testExceptionFromWithinTimeout() = runTest {
        expect(1)
        @Suppress("UNREACHABLE_CODE")
        try {
            expect(2)
            withTimeout(1.seconds) {
                expect(3)
                throw TestException()
            }
            expectUnreached()
        } catch (_: TestException) {
            finish(4)
        }
    }

    @Test
    fun testIncompleteWithTimeoutState() = runTest {
        lateinit var timeoutJob: Job
        val handle = withTimeout(Duration.INFINITE) {
            timeoutJob = coroutineContext[Job]!!
            timeoutJob.invokeOnCompletion { }
        }

        handle.dispose()
        timeoutJob.join()
        assertTrue(timeoutJob.isCompleted)
        assertFalse(timeoutJob.isActive)
        assertFalse(timeoutJob.isCancelled)
    }
}
