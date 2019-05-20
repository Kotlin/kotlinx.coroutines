package kotlinx.coroutines.flow.operation

import kotlinx.coroutines.TestBase
import kotlinx.coroutines.flow.*
import org.junit.Test
import kotlin.test.assertEquals

class DropOverflowTest : TestBase() {

    @Test
    fun testMaxInt() = runTest {
        val flow = (0..Int.MAX_VALUE).asFlow()
        assertEquals(Int.MAX_VALUE, flow.drop(Int.MAX_VALUE).single())
    }
}
