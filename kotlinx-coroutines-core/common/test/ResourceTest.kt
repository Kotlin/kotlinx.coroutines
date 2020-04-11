package kotlinx.coroutines

import kotlin.test.*

class ResourceTest {
    @Test
    fun testBasic() {
        var cancelCalled = 0
        val res = Resource<String>("OK") {
            cancelCalled++
        }
        assertEquals("OK", res.value)
        assertFalse(res.isCancelled)
        assertEquals(cancelCalled, 0)
        // Cancel is idempotent
        repeat(3) {
            res.cancel()
            assertEquals("OK", res.value)
            assertTrue(res.isCancelled)
            assertEquals(cancelCalled, 1)
        }
    }
}