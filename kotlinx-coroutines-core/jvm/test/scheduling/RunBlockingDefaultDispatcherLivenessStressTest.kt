package scheduling

import kotlinx.coroutines.*
import kotlinx.coroutines.scheduling.*
import kotlinx.coroutines.testing.*
import org.junit.*
import org.junit.runner.*
import org.junit.runners.*
import java.util.*
import java.util.concurrent.*

@RunWith(Parameterized::class)
class RunBlockingDefaultDispatcherLivenessStressTest(private val yieldMask: Int) : SchedulerTestBase() {
    init {
        corePoolSize = 1
    }

    companion object {
        @JvmStatic
        @Parameterized.Parameters
        fun data(): Array<Array<Any?>> {
            return Array(32 * stressTestMultiplierSqrt) { arrayOf(it) }
        }
    }

    @Test
    fun testLivenessOfDefaultDispatcher(): Unit = runBlocking {
        val oldRunBlockings = LinkedList<Job>()
        var maxOldRunBlockings = 0
        var busyWaits = 0
        repeat(5000 * stressTestMultiplierSqrt) {
            if (it % 1000 == 0) {
                System.err.println("======== $it, rb=${oldRunBlockings.size}, max rb=${maxOldRunBlockings}, busy=$busyWaits")
            }
            val barrier = CyclicBarrier(2)
            val barrier2 = CompletableDeferred<Unit>()
            val blocking = launch(dispatcher) {
                barrier.await()
                runBlocking {
                    if ((yieldMask and 1) != 0) yield()
                    barrier2.await()
                    if ((yieldMask and 2) != 0) yield()
                }
            }
            oldRunBlockings.addLast(blocking)
            val task = async(dispatcher) {
                if ((yieldMask and 4) != 0) yield()
                42.also {
                    if ((yieldMask and 8) != 0) yield()
                }
            }
            barrier.await()
            task.join()
            barrier2.complete(Unit)

            oldRunBlockings.removeIf(Job::isCompleted)
            while (oldRunBlockings.size > 5) {
                busyWaits++
                oldRunBlockings.removeIf(Job::isCompleted)
            }
            if (oldRunBlockings.size > maxOldRunBlockings) {
                maxOldRunBlockings = oldRunBlockings.size
            }
        }
    }
}