package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

class SafeFlowTest : TestBase() {

    @Test
    fun testEmissionsFromDifferentStateMachine() = runTest {
        val result = flow<Int> {
            emit1(1)
            emit2(2)
        }.onEach { yield() }.toList()
        assertEquals(listOf(1, 2), result)
        finish(3)
    }

    private suspend fun FlowCollector<Int>.emit1(expect: Int) {
        emit(expect)
        expect(expect)
    }

    private suspend fun FlowCollector<Int>.emit2(expect: Int) {
        emit(expect)
        expect(expect)
    }
}
