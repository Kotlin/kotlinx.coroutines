package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class LastTest : TestBase() {
    @Test
    fun testLast() = runTest {
        val flow = flowOf(1, 2, 3)
        assertEquals(3, flow.last())
        assertEquals(3, flow.lastOrNull())
    }

    @Test
    fun testNulls() = runTest {
        val flow = flowOf(1, null)
        assertNull(flow.last())
        assertNull(flow.lastOrNull())
    }

    @Test
    fun testNullsLastOrNull() = runTest {
        val flow = flowOf(null, 1)
        assertEquals(1, flow.lastOrNull())
    }

    @Test
    fun testEmptyFlow() = runTest {
        assertFailsWith<NoSuchElementException> { emptyFlow<Int>().last() }
        assertNull(emptyFlow<Int>().lastOrNull())
    }

    @Test
    fun testBadClass() = runTest {
        val instance = BadClass()
        val flow = flowOf(instance)
        assertSame(instance, flow.last())
        assertSame(instance, flow.lastOrNull())

    }
}
