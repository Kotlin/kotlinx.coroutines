
@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.experimental

import kotlin.test.*

class CommonWithTimeoutTest : TestBase() {
    /**
     * Tests a case of no timeout and no suspension inside.
     */
    @Test
    fun testBasicNoSuspend() = runTest {
        expect(1)
        val result = withTimeout(10_000) {
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
        val result = withTimeout(10_000) {
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
        launch(coroutineContext) {
            expect(4)
            yield() // back to main
            expect(7)
        }
        expect(2)
        // test that it does not yield to the above job when started
        val result = withTimeout(1000) {
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
        withTimeout(100) {
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
        withTimeout(100) {
            expect(2)
            // launch child with timeout
            launch(coroutineContext) {
                expect(4)
            }
            expect(3)
            // now will wait for child before returning
        }
        finish(5)
    }
}

