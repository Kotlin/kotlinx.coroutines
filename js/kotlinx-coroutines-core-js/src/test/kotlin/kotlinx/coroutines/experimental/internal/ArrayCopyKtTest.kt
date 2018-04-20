package kotlinx.coroutines.experimental.internal

import kotlin.test.*

class ArrayCopyTest {

    @Test
    fun testArrayCopy() {
        val source = Array(10, { it })
        val destination = arrayOfNulls<Int>(7)
        arraycopy(source, 2, destination, 1, 5)
        assertEquals(listOf(null, 2, 3, 4, 5, 6, null), destination.toList())
    }
}
