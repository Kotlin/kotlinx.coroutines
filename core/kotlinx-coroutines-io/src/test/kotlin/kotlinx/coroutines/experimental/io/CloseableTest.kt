package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Test
import org.junit.Assert.*

class CloseableTest : TestBase() {

    class TestCloseable: Closeable {
        internal var closed = false
        override suspend fun aClose() {
            closed = true
        }
        fun throwing(): Unit = throw RuntimeException()
        fun notThrowing() {}
    }

    @Test
    fun testNoExceptionThrown() = runBlocking {
        TestCloseable().let {
            it.use {
                it.notThrowing()
            }
            assertTrue(it.closed)
        }
    }

    @Test
    fun testExceptionThrown() = runBlocking {
        TestCloseable().let {
            try {
                it.use {
                    it.throwing()
                }
                fail()
            }
            catch (e: RuntimeException) {
                assertTrue(it.closed)
            }
        }
    }

}
