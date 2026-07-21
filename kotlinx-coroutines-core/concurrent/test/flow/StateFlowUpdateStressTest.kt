package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import kotlin.test.*

class StateFlowUpdateStressTest : TestBase() {
    private val iterations = 1_000_000 * stressTestMultiplier

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

        val j2 = launch(Dispatchers.Default) {
            repeat(iterations / 2) {
                flow.increment()
            }
        }

        joinAll(j1, j2)
        assertEquals(iterations, flow.value)
    }
}
