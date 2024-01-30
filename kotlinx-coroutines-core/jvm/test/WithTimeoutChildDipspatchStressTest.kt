package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.Test
import kotlin.test.*

class WithTimeoutChildDispatchStressTest : TestBase() {
    private val N_REPEATS = 10_000 * stressTestMultiplier

    /**
     * This stress-test makes sure that dispatching resumption from within withTimeout
     * works appropriately (without additional dispatch) despite the presence of
     * children coroutine in a different dispatcher.
     */
    @Test
    fun testChildDispatch() = runBlocking {
        repeat(N_REPEATS) {
            val result = withTimeout(5000) {
                // child in different dispatcher
                val job = launch(Dispatchers.Default) {
                    // done nothing, but dispatches to join from another thread
                }
                job.join()
                "DONE"
            }
            assertEquals("DONE", result)
        }
    }
}