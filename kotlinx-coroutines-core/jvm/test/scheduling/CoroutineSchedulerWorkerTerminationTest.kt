package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import kotlinx.coroutines.testing.TestBase
import kotlinx.coroutines.testing.stressTestMultiplier
import kotlinx.coroutines.testing.stressTestMultiplierSqrt
import kotlin.test.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.CountDownLatch
import java.util.concurrent.TimeUnit
import kotlin.time.Duration.Companion.milliseconds

class CoroutineSchedulerWorkerTerminationTest : TestBase() {

    @Test
    fun testWorkerTerminationDuringOversubscription() {
        repeat(25 * stressTestMultiplierSqrt) {
            doTest()
        }
    }

    /**
     * Emulates oversubscription + worker termination pattern.
     * What we want to recreate:
     * - IO worker
     * - CPU task in local queue
     * - No one to process it
     * - Termination of such worker
     */
    private fun doTest() {
        val corePoolSize = 2
        val tasksCount = corePoolSize + 1
        val dispatcher = SchedulerCoroutineDispatcher(
            corePoolSize,
            maxPoolSize = tasksCount,
            idleWorkerKeepAliveNs = TimeUnit.MILLISECONDS.toNanos(50)
        )
        val workers = ConcurrentHashMap.newKeySet<Thread>()
        val allWorkersCreated = CountDownLatch(tasksCount)
        val blockingTasksBlocker = CountDownLatch(1)
        val cpuThreads = ConcurrentHashMap.newKeySet<Thread>()
        val cpuThreadsReachedThis = CountDownLatch(corePoolSize)
        val cpuThreadsBlocked = CountDownLatch(1)
        val cpuThreadsFinished = CountDownLatch(tasksCount)
        val cpuScope = CoroutineScope(SupervisorJob() + dispatcher)
        fun recordWorker() {
            if (workers.add(Thread.currentThread())) allWorkersCreated.countDown()
        }
        repeat(tasksCount) {
            cpuScope.launch {
                // It would've been so much easier if a dispatch of a CPU task from a blocking thread
                // wouldn't been redirecting everything to the global queue.
                // Anyway: spam tasks until there are three blocking tasks properly created and blocking the whole scheduler.
                while (allWorkersCreated.count > 0) {
                    dispatcher.dispatchWithContext(Runnable {
                        recordWorker()
                        blockingTasksBlocker.await()
                    }, BlockingContext, false)
                    yield()
                }
                /*
                 * Before this line executes in any of the coroutines, the state we want is:
                 * - 3 out of 3 threads are blocked fully in the IO (BlockingContext) task
                 *- Each of these three threads has a CPU task in its local queue
                 *   (may not be true, the CPU task may be in the global queue, making the test non-deterministic)
                 * - These CPU tasks are, well, this very line of code
                 * - We release these blocking tasks, making this two out of three (!) executing
                 * - They record their thread and notify test coordinator
                 * - Test coordinator waits for the thread to shut down
                 * - Then releases 2 CPU tasks, 3rd one should execute
                 */
                cpuThreads += Thread.currentThread()
                cpuThreadsReachedThis.countDown()
                cpuThreadsBlocked.await()
                cpuThreadsFinished.countDown()
            }
        }
        allWorkersCreated.await() // Wait all
        blockingTasksBlocker.countDown() // Ublock all blocking
        cpuThreadsReachedThis.await() // Wait all
        // Quickly terminates, thanks keep alive timeout
        val retiringWorker = workers.single { it !in cpuThreads }
        retiringWorker.join()
        cpuThreadsBlocked.countDown() // Unblock
        cpuThreadsFinished.await(20, TimeUnit.SECONDS) // Wait, fail if we hit our regression
        dispatcher.close()
    }
}
