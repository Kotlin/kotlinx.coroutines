package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.flow.*
import org.junit.*

class ReusableContinuationStressTest : TestBase() {

    private val iterations = 1000 * stressTestMultiplierSqrt

    @Test // Originally reported by @denis-bezrukov in #2736
    fun testDebounceWithStateFlow() = runBlocking<Unit> {
        withContext(Dispatchers.Default) {
            repeat(iterations) {
                launch { // <- load the dispatcher and OS scheduler
                    runStressTestOnce(1, 1)
                }
            }
        }
    }

    private suspend fun runStressTestOnce(delay: Int, debounce: Int) = coroutineScope {
        val stateFlow = MutableStateFlow(0)
        val emitter = launch {
            repeat(1000) { i ->
                stateFlow.emit(i)
                delay(delay.toLong())
            }
        }
        var last = 0
        stateFlow.debounce(debounce.toLong()).take(100).collect { i ->
            if (i - last > 100) {
                last = i
            }
        }
        emitter.cancel()
    }
}
