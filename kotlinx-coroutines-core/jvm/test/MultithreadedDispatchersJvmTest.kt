package kotlinx.coroutines

import kotlinx.coroutines.internal.LocalAtomicInt
import kotlinx.coroutines.testing.*
import java.util.concurrent.ScheduledThreadPoolExecutor
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.test.*

class MultithreadedDispatchersJvmTest: TestBase() {
    /** Tests that the executor created in [newFixedThreadPoolContext] can not leak and be reconfigured. */
    @Test
    fun testExecutorReconfiguration() {
        newFixedThreadPoolContext(1, "test").apply {
            (executor as? ScheduledThreadPoolExecutor)?.corePoolSize = 2
        }.use { ctx ->
            val atomicInt = LocalAtomicInt(0)
            repeat(100) {
                ctx.dispatch(EmptyCoroutineContext, Runnable {
                    val entered = atomicInt.incrementAndGet()
                    Thread.yield() // allow other tasks to run
                    try {
                        check(entered == 1) { "Expected only one thread to be used, observed $entered" }
                    } finally {
                        atomicInt.decrementAndGet()
                    }
                })
            }
        }
    }
}
