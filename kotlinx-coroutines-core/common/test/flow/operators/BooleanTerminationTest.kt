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
    fun testAnyInfinite() = runTest {
        assertTrue(flow { while (true) { emit(5) } }.any { it == 5 })
    }

    @Test
    fun testAnyShortCircuit() = runTest {
        assertTrue(flow {
            emit(1)
            emit(2)
            expectUnreached()
        }.any {
            it == 2
        })
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
    fun testAllInfinite() = runTest {
        assertFalse(flow { while (true) { emit(5) } }.all { it == 0 })
    }

    @Test
    fun testAllShortCircuit() = runTest {
        assertFalse(flow {
            emit(1)
            emit(2)
            expectUnreached()
        }.all {
            it <= 1
        })
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

    @Test
    fun testNoneInfinite() = runTest {
        assertFalse(flow { while (true) { emit(5) } }.none { it == 5 })
    }

    @Test
    fun testNoneShortCircuit() = runTest {
        assertFalse(flow {
            emit(1)
            emit(2)
            expectUnreached()
        }.none {
            it == 2
        })
    }

}
