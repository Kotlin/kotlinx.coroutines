package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlin.test.*

class BooleanTerminationTest : TestBase() {
    @Test
    fun testAnyNominal() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
        }

        assertTrue(flow.any { it > 0 })
        assertTrue(flow.any { it % 2 == 0 })
        assertFalse(flow.any { it > 5 })
    }

    @Test
    fun testAnyEmpty() = runTest {
        assertFalse(emptyFlow<Int>().any { it > 0 })
    }

    @Test
    fun testAllNominal() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
        }

        assertTrue(flow.all { it > 0 })
        assertFalse(flow.all { it % 2 == 0 })
        assertFalse(flow.all { it > 5 })
    }

    @Test
    fun testAllEmpty() = runTest {
        assertTrue(emptyFlow<Int>().all { it > 0 })
    }

    @Test
    fun testNoneNominal() = runTest {
        val flow = flow {
            emit(1)
            emit(2)
        }

        assertFalse(flow.none { it > 0 })
        assertFalse(flow.none { it % 2 == 0 })
        assertTrue(flow.none { it > 5 })
    }

    @Test
    fun testNoneEmpty() = runTest {
        assertTrue(emptyFlow<Int>().none { it > 0 })
    }

}
