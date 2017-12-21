
@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlin.test.*

class CommonWithTimeoutOrNullTest : TestBase() {
    /**
     * Tests a case of no timeout and no suspension inside.
     */
    @Test
    fun testBasicNoSuspend() = runTest {
        expect(1)
        val result = withTimeoutOrNull(10_000) {
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
     * Tests property dispatching of `withTimeoutOrNull` blocks
     */
    @Test
    fun testDispatch() = runTest {
        expect(1)
        launch(coroutineContext) {
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
        expect(1)
        val result = withTimeoutOrNull(100) {
            while (true) {
                yield()
            }
        }
        assertEquals(null, result)
        finish(2)
    }

    @Test
    fun testInnerTimeoutTest() = runTest(
        expected = { it is CancellationException }
    ) {
        withTimeoutOrNull(200) {
            withTimeout(100) {
                while (true) {
                    yield()
                }
            }
            expectUnreached() // will timeout
        }
        expectUnreached() // will timeout
    }

    @Test
    fun testOuterTimeoutTest() = runTest {
        var counter = 0
        val result = withTimeoutOrNull(250) {
            while (true) {
                val inner = withTimeoutOrNull(100) {
                    while (true) {
                        yield()
                    }
                }
                assertEquals(null, inner)
                counter++
            }
        }
        assertEquals(null, result)
        // under load counter may be equal to 1, so the check is lenient here
        println("Executed: $counter times")
        check(counter in 1..2)
    }
}