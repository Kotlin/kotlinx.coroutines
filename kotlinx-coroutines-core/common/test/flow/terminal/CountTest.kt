package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class CountTest : TestBase() {
    @Test
    fun testCount() = runTest {
        val flow = flowOf(239, 240)
        assertEquals(2, flow.count())
        assertEquals(2, flow.count { true })
        assertEquals(1, flow.count { it % 2 == 0})
        assertEquals(0, flow.count { false })
    }

    @Test
    fun testNoValues() = runTest {
        assertEquals(0, flowOf<Int>().count())
        assertEquals(0, flowOf<Int>().count { false })
        assertEquals(0, flowOf<Int>().count { true })
    }

    @Test
    fun testException() = runTest {
        val flow = flow<Int> {
            throw TestException()
        }

        assertFailsWith<TestException> { flow.count() }
        assertFailsWith<TestException> { flow.count { false } }
    }

    @Test
    fun testExceptionAfterValue() = runTest {
        val flow = flow {
            emit(1)
            throw TestException()
        }

        assertFailsWith<TestException> { flow.count() }
        assertFailsWith<TestException> { flow.count { false } }
    }
}
