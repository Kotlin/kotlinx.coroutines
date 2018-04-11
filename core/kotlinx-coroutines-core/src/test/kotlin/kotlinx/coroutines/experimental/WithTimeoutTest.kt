
package kotlinx.coroutines.experimental

import kotlin.test.*
import java.io.IOException

class WithTimeoutTest : TestBase() {
    @Test
    fun testExceptionOnTimeout() = runTest {
        expect(1)
        try {
            withTimeout(100) {
                expect(2)
                delay(1000)
                expectUnreached()
                "OK"
            }
        } catch (e: CancellationException) {
            assertEquals("Timed out waiting for 100 MILLISECONDS", e.message)
            finish(3)
        }
    }

    @Test
    fun testSuppressExceptionWithResult() = runTest(
        expected = { it is CancellationException }
    ) {
        expect(1)
        val result = withTimeout(100) {
            expect(2)
            try {
                delay(1000)
            } catch (e: CancellationException) {
                finish(3)
            }
            "OK"
        }
        expectUnreached()
    }

    @Test
    fun testSuppressExceptionWithAnotherException() = runTest(
        expected = { it is IOException }
    ) {
        expect(1)
        withTimeout(100) {
            expect(2)
            try {
                delay(1000)
            } catch (e: CancellationException) {
                finish(3)
                throw IOException(e)
            }
            expectUnreached()
            "OK"
        }
        expectUnreached()
    }
}