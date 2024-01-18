package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlin.coroutines.*
import kotlin.test.*

class MultithreadedDispatcherStressTest {
    private val shared = atomic(0)

    /**
     * Tests that [newFixedThreadPoolContext] will not drop tasks when closed.
     */
    @Test
    fun testClosingNotDroppingTasks() {
        repeat(7) {
            shared.value = 0
            val nThreads = it + 1
            val dispatcher = newFixedThreadPoolContext(nThreads, "testMultiThreadedContext")
            repeat(1_000) {
                dispatcher.dispatch(EmptyCoroutineContext, Runnable {
                    shared.incrementAndGet()
                })
            }
            dispatcher.close()
            while (shared.value < 1_000) {
                // spin.
                // the test will hang here if the dispatcher drops tasks.
            }
        }
    }
}
