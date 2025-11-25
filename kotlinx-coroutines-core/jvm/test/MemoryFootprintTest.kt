package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.Test
import org.openjdk.jol.info.*
import kotlin.test.*


class MemoryFootprintTest : TestBase(true) {

    @Test
    fun testJobLayout() = assertLayout(Job().javaClass, 32)

    @Test
    fun testJobSize() {
        assertTotalSize(jobWithChildren(1), 128) // + 8
        assertTotalSize(jobWithChildren(2), 216) // + 16
        assertTotalSize(jobWithChildren(3), 280) // + 32
        assertTotalSize(jobWithChildren(4), 344) // + 40
    }

    private fun jobWithChildren(numberOfChildren: Int): Job {
        val result = Job()
        repeat(numberOfChildren) {
            Job(result)
        }
        return result
    }

    @Test
    fun testCancellableContinuationFootprint() = assertLayout(CancellableContinuationImpl::class.java, 48)

    private fun assertLayout(clz: Class<*>, expectedSize: Int) {
        val size = ClassLayout.parseClass(clz).instanceSize()
//        println(ClassLayout.parseClass(clz).toPrintable())
        assertEquals(expectedSize.toLong(), size)
    }

    private fun assertTotalSize(instance: Job, expectedSize: Int) {
        val size = GraphLayout.parseInstance(instance).totalSize()
        assertEquals(expectedSize.toLong(), size)
    }
}
