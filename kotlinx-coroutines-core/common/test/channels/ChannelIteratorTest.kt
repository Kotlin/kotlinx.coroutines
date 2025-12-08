package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlin.test.*

class ChannelIteratorTest : TestBase() {
    @Test
    fun testIteratorClosedHasNextFalse() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Int>()
            val iterator = channel.iterator()
            channel.close()
            assertFalse(iterator.hasNext())
        }
    }

    @Test
    fun testIteratorClosedWithExceptionHasNextThrows() = runTest {
        TestChannelKind.entries.forEach { kind ->
            val channel = kind.create<Int>()
            val iterator = channel.iterator()
            channel.close(TestException())
            assertFailsWith<TestException> { iterator.hasNext() }
        }
    }
}
