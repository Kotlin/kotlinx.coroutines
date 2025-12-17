@file:Suppress("PackageDirectoryMismatch")

package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlin.test.*

class AsFlowTest : TestBase() {
    @Test
    fun testAsFlow() = runTest {
        val mutableSharedFlow = MutableSharedFlow<Int>(replay = 3)
        mutableSharedFlow.emit(value = 1)
        mutableSharedFlow.emit(value = 2)
        mutableSharedFlow.emit(value = 3)

        val flow = mutableSharedFlow.asFlow()

        assertEquals(
            expected = listOf(1, 2, 3),
            actual = flow
                .take(count = 3)
                .toList(),
        )
    }

    @Test
    fun testAsFlowIsNotSharedFlow() {
        val mutableSharedFlow = MutableSharedFlow<Int>()

        val flow = mutableSharedFlow.asFlow()

        assertIsNot<SharedFlow<Int>>(flow)
    }
}
