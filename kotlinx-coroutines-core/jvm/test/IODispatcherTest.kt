package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.Test
import kotlin.test.*

class IODispatcherTest : TestBase() {
    @Test
    fun testWithIOContext() = runTest {
        // just a very basic test that is dispatcher works and indeed uses background thread
        val mainThread = Thread.currentThread()
        expect(1)
        withContext(Dispatchers.IO) {
            expect(2)
            assertNotSame(mainThread, Thread.currentThread())
        }

        expect(3)
        assertSame(mainThread, Thread.currentThread())
        finish(4)
    }
}