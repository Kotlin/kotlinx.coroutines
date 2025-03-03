package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

class ThreadContextMutableCopiesConcurrentTest : TestBase() {
    @Test
    fun testDataIsCopiedForRunBlocking() = runTest {
        val root = ThreadContextMutableCopiesTest.MyMutableElement(ArrayList())
        val originalData = root.mutableData
        runBlocking(root) {
            assertNotSame(originalData, ThreadContextMutableCopiesTest.Companion.threadLocalData.get())
        }
    }
}
