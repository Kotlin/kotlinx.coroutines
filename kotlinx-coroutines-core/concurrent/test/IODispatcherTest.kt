@file:OptIn(ExperimentalThreadBlockingApi::class)

package kotlinx.coroutines

import kotlinx.atomicfu.locks.*
import kotlinx.coroutines.testing.*
import kotlin.test.*

class IODispatcherTest : TestBase() {
    @Test
    fun testWithIOContext() = runTest {
        // just a very basic test that is dispatcher works and indeed uses background thread
        val mainThread = ParkingSupport.currentThreadHandle()
        expect(1)
        withContext(Dispatchers.IO) {
            expect(2)
            assertNotSame(mainThread, ParkingSupport.currentThreadHandle())
        }

        expect(3)
        assertSame(mainThread, ParkingSupport.currentThreadHandle())
        finish(4)
    }
}
