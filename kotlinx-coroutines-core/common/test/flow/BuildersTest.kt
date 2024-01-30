package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class BuildersTest : TestBase() {

    @Test
    fun testSuspendLambdaAsFlow() = runTest {
        val lambda = suspend { 42 }
        assertEquals(42, lambda.asFlow().single())
    }

    @Test
    fun testRangeAsFlow() = runTest {
        assertEquals((0..9).toList(), (0..9).asFlow().toList())
        assertEquals(emptyList(), (0..-1).asFlow().toList())

        assertEquals((0L..9L).toList(), (0L..9L).asFlow().toList())
        assertEquals(emptyList(), (0L..-1L).asFlow().toList())
    }

    @Test
    fun testArrayAsFlow() = runTest {
        assertEquals((0..9).toList(), IntArray(10) { it }.asFlow().toList())
        assertEquals(emptyList(), intArrayOf().asFlow().toList())

        assertEquals((0L..9L).toList(), LongArray(10) { it.toLong() }.asFlow().toList())
        assertEquals(emptyList(), longArrayOf().asFlow().toList())
    }

    @Test
    fun testSequence() = runTest {
        val expected = (0..9).toList()
        assertEquals(expected, expected.iterator().asFlow().toList())
        assertEquals(expected, expected.asIterable().asFlow().toList())
    }
}
