package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

class WithDefaultContextTest : TestBase() {
    @Test
    fun testNoSuspend() = runTest {
        expect(1)
        val result = withContext(Dispatchers.Default) {
            expect(2)
            "OK"
        }
        assertEquals("OK", result)
        finish(3)
    }

    @Test
    fun testWithSuspend() = runTest {
        expect(1)
        val result = withContext(Dispatchers.Default) {
            expect(2)
            delay(100)
            expect(3)
            "OK"
        }
        assertEquals("OK", result)
        finish(4)
    }
}