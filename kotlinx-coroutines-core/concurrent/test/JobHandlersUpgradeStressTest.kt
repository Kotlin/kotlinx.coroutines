package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.coroutines.testing.*
import kotlin.concurrent.*
import kotlin.random.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

class JobHandlersUpgradeStressTest : TestBase() {
    private val nSeconds = 3 * stressTestMultiplier
    private val nThreads = 4

    private val cyclicBarrier = ConcurrentCyclicBarrier(1 + nThreads)
    private val threads = mutableListOf<ConcurrentThread>()

    private val inters = atomic(0)
    private val removed = atomic(0)
    private val fired = atomic(0)

    private val sink = atomic(0)

    @Volatile
    private var done = false

    @Volatile
    private var job: Job? = null

    internal class State {
        val state = atomic(0)
    }

    /**
     * Tests handlers not being invoked more than once.
     */
    @Test
    fun testStress() {
        println("--- JobHandlersUpgradeStressTest")
        threads += ConcurrentThread("creator") {
            while (true) {
                job = if (done) null else Job()
                cyclicBarrier.await()
                val job = job ?: break
                // burn some time
                repeat(Random.nextInt(3000)) { sink.incrementAndGet() }
                // cancel job
                job.cancel()
                cyclicBarrier.await()
                inters.incrementAndGet()
            }
        }
        threads += List(nThreads) { threadId ->
            ConcurrentThread(name = "handler-$threadId") {
                while (true) {
                    val onCancelling = Random.nextBoolean()
                    val invokeImmediately: Boolean = Random.nextBoolean()
                    cyclicBarrier.await()
                    val job = job ?: break
                    val state = State()
                    // burn some time
                    repeat(Random.nextInt(1000)) { sink.incrementAndGet() }
                    val handle =
                        job.invokeOnCompletion(onCancelling = onCancelling, invokeImmediately = invokeImmediately) {
                            if (!state.state.compareAndSet(0, 1))
                                error("Fired more than once or too late: state=${state.state.value}")
                        }
                    // burn some time
                    repeat(Random.nextInt(1000)) { sink.incrementAndGet() }
                    // dispose
                    handle.dispose()
                    cyclicBarrier.await()
                    val resultingState = state.state.value
                    when (resultingState) {
                        0 -> removed.incrementAndGet()
                        1 -> fired.incrementAndGet()
                        else -> error("Cannot happen")
                    }
                    if (!state.state.compareAndSet(resultingState, 2))
                        error("Cannot fire late: resultingState=$resultingState")
                }
            }
        }
        threads.forEach { it.start() }
        repeat(nSeconds) { second ->
            threadSleep(1.seconds)
            println("${second + 1}: ${inters.value} iterations")
        }
        done = true
        threads.forEach { it.join() }
        println("        Completed ${inters.value} iterations")
        println("  Removed handler ${removed.value} times")
        println("    Fired handler ${fired.value} times")
    }
}
