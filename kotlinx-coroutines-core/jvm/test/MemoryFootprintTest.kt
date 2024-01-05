package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.Test
import org.openjdk.jol.info.ClassLayout
import kotlin.test.*


class MemoryFootprintTest : TestBase(true) {

    @Test
    fun testJobLayout() = assertLayout(Job().javaClass, 24)

    @Test
    fun testCancellableContinuationFootprint() = assertLayout(CancellableContinuationImpl::class.java, 48)

    private fun assertLayout(clz: Class<*>, expectedSize: Int) {
        val size = ClassLayout.parseClass(clz).instanceSize()
//        println(ClassLayout.parseClass(clz).toPrintable())
        assertEquals(expectedSize.toLong(), size)
    }
}
