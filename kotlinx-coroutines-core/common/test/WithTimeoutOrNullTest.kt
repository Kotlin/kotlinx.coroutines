@file:Suppress("ConvertLongToDuration")

package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class WithTimeoutOrNullTest : TestBase() {
    /**
     * Tests a case of no timeout and no suspension inside.
     */
    @Test
    fun testBasicNoSuspend() = runTest {
        expect(1)
        val result = withTimeoutOrNull(1) {
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
        val result = withTimeoutOrNull(10_000) {
            expect(2)
            yield()
            expect(3)
            "OK"
        }
        assertEquals("OK", result)
        finish(4)
    }

    /**
     * Tests proper dispatching of `withTimeoutOrNull` blocks
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
        val result = withTimeoutOrNull(1000) {
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
    fun testYieldBlockingWithTimeout() = runTest {
        val result = withTimeoutOrNull(100) {
            while (true) {
                yield()
            }
        }
        assertNull(result)
    }

    @Test
    fun testSmallTimeout() = runTest {
        val channel = Channel<Int>(1)
        val value = withTimeoutOrNull(1) {
            channel.receive()
        }
        assertNull(value)
    }

    @Test
    fun testThrowException() = runTest {
        assertFailsWith<AssertionError> {
            withTimeoutOrNull(Long.MAX_VALUE) {
                throw AssertionError()
            }
        }
    }

    @Test
    fun testInnerTimeout() = withVirtualTime {
        assertFailsWith<TimeoutCancellationException> {
            withTimeoutOrNull(1000) {
                withTimeout(10) {
                    awaitCancellation()
                }
            }
        }
        finish(1)
    }

    @Test
    fun testOuterTimeout() = withVirtualTime {
        var counter = 0
        val result = withTimeoutOrNull(320) {
            while (true) {
                val inner = withTimeoutOrNull(150) {
                    awaitCancellation()
                }
                assertNull(inner)
                counter++
            }
        }
        assertNull(result)
        assertEquals(2, counter)
        finish(1)
    }

    @Test
    fun testBadClass() = runTest {
        val bad = BadClass()
        val result = withTimeoutOrNull(1) {
            bad
        }
        assertSame(bad, result)
    }

    @Test
    fun testNullOnTimeout() = runTest {
        expect(1)
        val result = withTimeoutOrNull(100) {
            expect(2)
            delay(1000)
            expectUnreached()
        }
        assertNull(result)
        finish(3)
    }

    @Test
    fun testSuppressExceptionWithResult() = runTest {
        expect(1)
        // Assert that withTimeoutOrNull returns null
        // even if the block catches the cancellation and returns a result.
        val result = withTimeoutOrNull(100) {
            expect(2)
            assertFailsWith<TimeoutCancellationException> {
                expect(3)
                delay(1000)
                expectUnreached()
            }
            expect(4)
            "OK"
        }
        assertNull(result)
        finish(5)
    }

    @Test
    fun testSuppressExceptionWithAnotherException() = runTest {
        expect(1)
        assertFailsWith<TestException> {
            withTimeoutOrNull(100) {
                expect(2)
                assertFailsWith<TimeoutCancellationException> {
                    delay(1000)
                }
                expect(3)
                throw TestException()
            }
        }
        finish(4)
    }

    @Test
    fun testNegativeTimeout() = runTest {
        var result = withTimeoutOrNull(-1) {
            expectUnreached()
        }
        assertNull(result)
        result = withTimeoutOrNull(0) {
            expectUnreached()
        }
        assertNull(result)
    }

    @Test
    fun testExceptionFromWithinTimeout() = runTest {
        assertFailsWith<TestException> {
            withTimeoutOrNull(1000) {
                throw TestException()
            }
        }
    }
}
