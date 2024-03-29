package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

// A simplified version of StateFlowUpdateStressTest
class StateFlowUpdateCommonTest : TestBase() {
    private val iterations = 100_000 * stressTestMultiplier

    @Test
    fun testUpdate() = doTest { update { it + 1 } }

    @Test
    fun testUpdateAndGet() = doTest { updateAndGet { it + 1 } }

    @Test
    fun testGetAndUpdate() = doTest { getAndUpdate { it + 1 } }

    private fun doTest(increment: MutableStateFlow<Int>.() -> Unit) = runTest {
        val flow = MutableStateFlow(0)
        val j1 = launch(Dispatchers.Default) {
            repeat(iterations / 2) {
                flow.increment()
            }
        }

        repeat(iterations / 2) {
            flow.increment()
        }

        joinAll(j1)
        assertEquals(iterations, flow.value)
    }
}
