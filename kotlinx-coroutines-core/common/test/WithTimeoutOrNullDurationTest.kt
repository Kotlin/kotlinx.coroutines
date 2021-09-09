
/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import kotlin.test.*
import kotlin.time.*

@ExperimentalTime
class WithTimeoutOrNullDurationTest : TestBase() {
    /**
     * Tests a case of no timeout and no suspension inside.
     */
    @Test
    fun testBasicNoSuspend() = runTest {
        expect(1)
        val result = withTimeoutOrNull(Duration.seconds(10)) {
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
        val result = withTimeoutOrNull(Duration.seconds(10)) {
            expect(2)
            yield()
            expect(3)
            "OK"
        }
        assertEquals("OK", result)
        finish(4)
    }

    /**
     * Tests property dispatching of `withTimeoutOrNull` blocks
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
        val result = withTimeoutOrNull(Duration.seconds(1)) {
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
        expect(1)
        val result = withTimeoutOrNull(Duration.milliseconds(100)) {
            while (true) {
                yield()
            }
        }
        assertNull(result)
        finish(2)
    }

    @Test
    fun testSmallTimeout() = runTest {
        val channel = Channel<Int>(1)
        val value = withTimeoutOrNull(Duration.milliseconds(1)) {
            channel.receive()
        }
        assertNull(value)
    }

    @Test
    fun testThrowException() = runTest(expected = {it is AssertionError}) {
        withTimeoutOrNull<Unit>(Duration.INFINITE) {
            throw AssertionError()
        }
    }

    @Test
    fun testInnerTimeout() = runTest(
        expected = { it is CancellationException }
    ) {
        withTimeoutOrNull(Duration.milliseconds(1000)) {
            withTimeout(Duration.milliseconds(10)) {
                while (true) {
                    yield()
                }
            }
            @Suppress("UNREACHABLE_CODE")
            expectUnreached() // will timeout
        }
        expectUnreached() // will timeout
    }

    @Test
    fun testNestedTimeout() = runTest(expected = { it is TimeoutCancellationException }) {
        withTimeoutOrNull(Duration.INFINITE) {
            // Exception from this withTimeout is not suppressed by withTimeoutOrNull
            withTimeout(Duration.milliseconds(10)) {
                delay(Duration.INFINITE)
                1
            }
        }

        expectUnreached()
    }

    @Test
    fun testOuterTimeout() = runTest {
        var counter = 0
        val result = withTimeoutOrNull(Duration.milliseconds(250)) {
            while (true) {
                val inner = withTimeoutOrNull(Duration.milliseconds(100)) {
                    while (true) {
                        yield()
                    }
                }
                assertNull(inner)
                counter++
            }
        }
        assertNull(result)
        check(counter in 1..2) {"Executed: $counter times"}
    }

    @Test
    fun testBadClass() = runTest {
        val bad = BadClass()
        val result = withTimeoutOrNull(Duration.milliseconds(100)) {
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
    fun testNullOnTimeout() = runTest {
        expect(1)
        val result = withTimeoutOrNull(Duration.milliseconds(100)) {
            expect(2)
            delay(Duration.milliseconds(1000))
            expectUnreached()
            "OK"
        }
        assertNull(result)
        finish(3)
    }

    @Test
    fun testSuppressExceptionWithResult() = runTest {
        expect(1)
        val result = withTimeoutOrNull(Duration.milliseconds(100)) {
            expect(2)
            try {
                delay(Duration.milliseconds(1000))
            } catch (e: CancellationException) {
                expect(3)
            }
            "OK"
        }
        assertNull(result)
        finish(4)
    }

    @Test
    fun testSuppressExceptionWithAnotherException() = runTest {
        expect(1)
        try {
            withTimeoutOrNull(Duration.milliseconds(100)) {
                expect(2)
                try {
                    delay(Duration.milliseconds(1000))
                } catch (e: CancellationException) {
                    expect(3)
                    throw TestException()
                }
                expectUnreached()
                "OK"
            }
            expectUnreached()
        } catch (e: TestException) {
            // catches TestException
            finish(4)

        }
    }

    @Test
    fun testNegativeTimeout() = runTest {
        expect(1)
        var result = withTimeoutOrNull(-Duration.milliseconds(1)) {
            expectUnreached()
        }
        assertNull(result)
        result = withTimeoutOrNull(Duration.milliseconds(0)) {
            expectUnreached()
        }
        assertNull(result)
        finish(2)
    }

    @Test
    fun testExceptionFromWithinTimeout() = runTest {
        expect(1)
        try {
            expect(2)
            withTimeoutOrNull<Unit>(Duration.milliseconds(1000)) {
                expect(3)
                throw TestException()
            }
            expectUnreached()
        } catch (e: TestException) {
            finish(4)
        }
    }
}
