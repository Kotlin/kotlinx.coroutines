package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlin.test.*

class DropFirstTest : TestBase() {

    @Test
    fun testDropFirst() = runTest {
        val flow = flowOf(1, 2, 3)

        val result = flow.dropFirst()

        assertEquals(
            expected = listOf(2, 3),
            actual = result.toList(),
        )
    }

    @Test
    fun testDropFirstOnEmpty() = runTest {
        val flow = emptyFlow<Int>()

        val result = flow.dropFirst()

        assertEquals(
            expected = emptyList(),
            actual = result.toList(),
        )
    }

    @Test
    fun testDropFirstOnSingle() = runTest {
        val flow = flowOf(1)

        val result = flow.dropFirst()

        assertEquals(
            expected = emptyList(),
            actual = result.toList(),
        )
    }
}
