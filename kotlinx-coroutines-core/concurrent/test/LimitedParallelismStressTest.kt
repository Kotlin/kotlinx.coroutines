@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines

import kotlinx.coroutines.exceptions.yieldThread
import kotlinx.coroutines.testing.*
import kotlin.concurrent.atomics.*
import kotlin.coroutines.*
import kotlin.random.Random
import kotlin.test.*
import kotlin.time.Duration.Companion.milliseconds

class LimitedParallelismStressTest1 : LimitedParallelismStressTest(1)
class LimitedParallelismStressTest2 : LimitedParallelismStressTest(2)
class LimitedParallelismStressTest3 : LimitedParallelismStressTest(3)
class LimitedParallelismStressTest4 : LimitedParallelismStressTest(4)


abstract class LimitedParallelismStressTest(private val targetParallelism: Int) : TestBase() {
    private val iterations = 100_000

    private val parallelism = AtomicInt(0)

    private fun checkParallelism() {
        val value = parallelism.incrementAndFetch()
        yieldThread()
        assertTrue { value <= targetParallelism }
        parallelism.decrementAndFetch()
    }

    @Test
    fun testLimitedExecutor() = runTest {
        newFixedThreadPoolContext(targetParallelism * 2, "test").use { executor ->
            val view = executor.limitedParallelism(targetParallelism)
            doStress {
                repeat(iterations) {
                    launch(view) {
                        checkParallelism()
                    }
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
        newFixedThreadPoolContext(targetParallelism * 2, "test").use { executor ->
            val view = executor.limitedParallelism(targetParallelism)
            doStress {
                repeat(iterations) {
                    val barrier = ConcurrentCyclicBarrier(targetParallelism + 1)
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
    }

    /**
     * Checks that dispatcher failures during fairness redispatches don't prevent reaching the target parallelism.
     */
    @Test
    fun testLimitedFailingDispatcherReachesTargetParallelism() = runTest {
        newFixedThreadPoolContext(targetParallelism * 2, "test").use { executor ->
            val keepFailing = AtomicBoolean(true)
            val occasionallyFailing = object : CoroutineDispatcher() {
                override fun dispatch(context: CoroutineContext, block: Runnable) {
                    if (keepFailing.load() && Random.nextBoolean()) throw TestException()
                    executor.dispatch(context, block)
                }
            }.limitedParallelism(targetParallelism)
            doStress {
                repeat(1000) {
                    keepFailing.store(true) // we want the next tasks to sporadically fail
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
                    keepFailing.store(false) // we want the next tasks to succeed
                    val barrier = ConcurrentCyclicBarrier(targetParallelism + 1)
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
                        concurrentSleep(1.milliseconds)
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
    }

    private suspend inline fun doStress(crossinline block: suspend CoroutineScope.() -> Unit) {
        repeat(stressTestMultiplier) {
            coroutineScope {
                block()
            }
        }
    }
}
