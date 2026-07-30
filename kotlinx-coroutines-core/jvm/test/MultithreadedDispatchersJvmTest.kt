package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import java.util.concurrent.ScheduledThreadPoolExecutor
import kotlin.concurrent.atomics.AtomicInt
import kotlin.concurrent.atomics.ExperimentalAtomicApi
import kotlin.concurrent.atomics.decrementAndFetch
import kotlin.concurrent.atomics.incrementAndFetch
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.test.*

class MultithreadedDispatchersJvmTest: TestBase() {
    /** Tests that the executor created in [newFixedThreadPoolContext] can not leak and be reconfigured. */
    @OptIn(ExperimentalAtomicApi::class)
    @Test
    fun testExecutorReconfiguration() {
        newFixedThreadPoolContext(1, "test").apply {
            (executor as? ScheduledThreadPoolExecutor)?.corePoolSize = 2
        }.use { ctx ->
            val atomicInt = AtomicInt(0)
            repeat(100) {
                ctx.dispatch(EmptyCoroutineContext, Runnable {
                    val entered = atomicInt.incrementAndFetch()
                    Thread.yield() // allow other tasks to run
                    try {
                        check(entered == 1) { "Expected only one thread to be used, observed $entered" }
                    } finally {
                        atomicInt.decrementAndFetch()
                    }
                })
            }
        }
    }
}
