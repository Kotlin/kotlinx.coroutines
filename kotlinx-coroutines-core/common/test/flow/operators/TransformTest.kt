package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class TransformTest : TestBase() {
    @Test
    fun testDoubleEmit() = runTest {
         val flow = flowOf(1, 2, 3)
             .transform {
                 emit(it)
                 emit(it)
             }
        assertEquals(listOf(1, 1, 2, 2, 3, 3), flow.toList())
    }
}