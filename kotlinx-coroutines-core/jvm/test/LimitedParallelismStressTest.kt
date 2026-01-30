package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import java.util.concurrent.*
import java.util.concurrent.atomic.*
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.test.*

@RunWith(Parameterized::class)
class LimitedParallelismStressTest(private val targetParallelism: Int) : TestBase() {

    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = listOf(1, 2, 3, 4).map { arrayOf(it) }
    }

    @get:Rule
    val executor = ExecutorRule(targetParallelism * 2)
    private val iterations = 100_000

    private val parallelism = AtomicInteger(0)

    private fun checkParallelism() {
        val value = parallelism.incrementAndGet()
        Thread.yield()
        assertTrue { value <= targetParallelism }
        parallelism.decrementAndGet()
    }

    @Test
    fun testLimitedExecutor() = runTest {
        val view = executor.limitedParallelism(targetParallelism)
        doStress {
            repeat(iterations) {
                launch(view) {
                    checkParallelism()
                }
            }
        }
    }

    @Test
    fun testLimitedDispatchersIo() = runTest {
        val view = Dispatchers.IO.limitedParallelism(targetParallelism)
        doStress {
            repeat(iterations) {
                launch(view) {
                    checkParallelism()
                }
            }
        }
    }

    @Test
    fun testLimitedDispatchersIoDispatchYield() = runTest {
        val view = Dispatchers.IO.limitedParallelism(targetParallelism)
        doStress {
            launch(view) {
                yield()
                checkParallelism()
            }
        }
    }

    @Test
    fun testLimitedExecutorReachesTargetParallelism() = runTest {
        val view = executor.limitedParallelism(targetParallelism)
        doStress {
            repeat(iterations) {
                val barrier = CyclicBarrier(targetParallelism + 1)
                repeat(targetParallelism) {
                    launch(view) {
                        barrier.await()
                    }
                }
                // Successfully awaited parallelism + 1
                barrier.await()
                coroutineContext.job.children.toList().joinAll()
            }
        }
    }

    /**
     * Checks that dispatcher failures during fairness redispatches don't prevent reaching the target parallelism.
     */
    @Test
    fun testLimitedFailingDispatcherReachesTargetParallelism() = runTest {
        val keepFailing = AtomicBoolean(true)
        val occasionallyFailing = object: CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                if (keepFailing.get() && ThreadLocalRandom.current().nextBoolean()) throw TestException()
                executor.dispatch(context, block)
            }
        }.limitedParallelism(targetParallelism)
        doStress {
            repeat(1000) {
                keepFailing.set(true) // we want the next tasks to sporadically fail
                // Start some tasks to make sure redispatching for fairness is happening
                repeat(targetParallelism * 16 + 1) {
                    // targetParallelism * 16 + 1 because we need at least one worker to go through a fairness yield
                    // with high probability.
                    try {
                        occasionallyFailing.dispatch(EmptyCoroutineContext, Runnable {
                            // do nothing.
                        })
                    } catch (_: DispatchException) {
                        // ignore
                    }
                }
                keepFailing.set(false) // we want the next tasks to succeed
                val barrier = CyclicBarrier(targetParallelism + 1)
                repeat(targetParallelism) {
                    launch(occasionallyFailing) {
                        barrier.await()
                    }
                }
                val success = launch(Dispatchers.Default) {
                    // Successfully awaited parallelism + 1
                    barrier.await()
                }
                // Feed the dispatcher with more tasks to make sure it's not stuck
                while (success.isActive) {
                    Thread.sleep(1)
                    repeat(targetParallelism) {
                        occasionallyFailing.dispatch(EmptyCoroutineContext, Runnable {
                            // do nothing.
                        })
                    }
                }
                coroutineContext.job.children.toList().joinAll()
            }
        }
    }

    private suspend inline fun doStress(crossinline block: suspend CoroutineScope.() -> Unit) {
        repeat(stressTestMultiplier) {
            coroutineScope {
                block()
            }
        }
    }
}
