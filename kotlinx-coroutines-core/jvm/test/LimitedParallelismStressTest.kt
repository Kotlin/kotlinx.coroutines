package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import java.util.concurrent.*
import java.util.concurrent.atomic.*
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

    private suspend inline fun doStress(crossinline block: suspend CoroutineScope.() -> Unit) {
        repeat(stressTestMultiplier) {
            coroutineScope {
                block()
            }
        }
    }
}
