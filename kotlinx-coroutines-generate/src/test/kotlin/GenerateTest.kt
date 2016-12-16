
import kotlinx.coroutines.generate
import org.junit.Test
import java.util.*
import kotlin.test.assertEquals
import kotlin.test.assertFails
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class GenerateTest {
    @Test
    fun testSimple() {
        val result = generate {
            for (i in 1..3) {
                yield(2 * i)
            }
        }

        assertEquals(listOf(2, 4, 6), result.toList())
        // Repeated calls also work
        assertEquals(listOf(2, 4, 6), result.toList())
    }

    @Test
    fun testCallHasNextSeveralTimes() {
        val result = generate {
            yield(1)
        }

        val iterator = result.iterator()

        assertTrue(iterator.hasNext())
        assertTrue(iterator.hasNext())
        assertTrue(iterator.hasNext())

        assertEquals(1, iterator.next())

        assertFalse(iterator.hasNext())
        assertFalse(iterator.hasNext())
        assertFalse(iterator.hasNext())

        assertTrue(assertFails { iterator.next() } is NoSuchElementException)
    }

    @Test
    fun testManualIteration() {
        val result = generate {
            yield(1)
            yield(2)
            yield(3)
        }

        val iterator = result.iterator()

        assertTrue(iterator.hasNext())
        assertTrue(iterator.hasNext())
        assertEquals(1, iterator.next())

        assertTrue(iterator.hasNext())
        assertTrue(iterator.hasNext())
        assertEquals(2, iterator.next())

        assertEquals(3, iterator.next())

        assertFalse(iterator.hasNext())
        assertFalse(iterator.hasNext())

        assertTrue(assertFails { iterator.next() } is NoSuchElementException)

        assertEquals(1, result.iterator().next())
    }

    @Test
    fun testEmptySequence() {
        val result = generate<Int> {}
        val iterator = result.iterator()

        assertFalse(iterator.hasNext())
        assertFalse(iterator.hasNext())

        assertTrue(assertFails { iterator.next() } is NoSuchElementException)
    }

    @Test
    fun testLaziness() {
        var sharedVar = -2
        val result = generate {
            while (true) {
                when (sharedVar) {
                    -1 -> return@generate
                    -2 -> error("Invalid state: -2")
                    else -> yield(sharedVar)
                }
            }
        }

        val iterator = result.iterator()

        sharedVar = 1
        assertTrue(iterator.hasNext())
        assertEquals(1, iterator.next())

        sharedVar = 2
        assertTrue(iterator.hasNext())
        assertEquals(2, iterator.next())

        sharedVar = 3
        assertTrue(iterator.hasNext())
        assertEquals(3, iterator.next())

        sharedVar = -1
        assertFalse(iterator.hasNext())
        assertTrue(assertFails { iterator.next() } is NoSuchElementException)
    }

    @Test
    fun testExceptionInCoroutine() {
        var sharedVar = -2
        val result = generate {
            while (true) {
                when (sharedVar) {
                    -1 -> return@generate
                    -2 -> error("Invalid state: -2")
                    else -> yield(sharedVar)
                }
            }
        }

        val iterator = result.iterator()

        sharedVar = 1
        assertEquals(1, iterator.next())

        sharedVar = -2
        assertTrue(assertFails { iterator.hasNext() } is IllegalStateException)
    }

    @Test
    fun testParallelIteration() {
        var inc = 0
        val result = generate {
            for (i in 1..3) {
                inc++
                yield(inc * i)
            }
        }

        assertEquals(listOf(Pair(1, 2), Pair(6, 8), Pair(15, 18)), result.zip(result).toList())
    }
}
