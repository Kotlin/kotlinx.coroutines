package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlin.test.*

class ChannelIteratorTest : ChannelTestBase() {
    @Test
    fun testIteratorClosedHasNextFalse() = runTestForEach { kind ->
        val channel = kind.create<Int>()
        val iterator = channel.iterator()
        channel.close()
        assertFalse(iterator.hasNext())
    }

    @Test
    fun testIteratorClosedWithExceptionHasNextThrows() = runTestForEach { kind ->
        val channel = kind.create<Int>()
        val iterator = channel.iterator()
        channel.close(TestException())
        assertFailsWith<TestException> { (iterator.hasNext()) }
    }
}
