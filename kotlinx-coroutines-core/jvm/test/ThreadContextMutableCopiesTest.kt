package kotlinx.coroutines

import kotlinx.coroutines.CommonThreadContextMutableCopiesTest.*
import kotlinx.coroutines.CommonThreadContextMutableCopiesTest.Companion.threadLocalData
import kotlinx.coroutines.testing.*
import kotlin.test.*

class ThreadContextMutableCopiesTest : TestBase() {
    @Test
    fun testDataIsCopiedForRunBlocking() = runTest {
        val root = MyMutableElement(ArrayList())
        val originalData = root.mutableData
        runBlocking(root) {
            assertNotSame(originalData, threadLocalData.get())
        }
    }
}
