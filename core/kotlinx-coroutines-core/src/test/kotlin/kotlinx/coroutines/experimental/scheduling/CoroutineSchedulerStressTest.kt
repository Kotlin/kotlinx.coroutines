package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.*
import org.junit.After
import org.junit.Test
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.CountDownLatch
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicLong
import kotlin.coroutines.experimental.EmptyCoroutineContext
import kotlin.test.assertEquals

class CoroutineSchedulerStressTest : TestBase() {

    private var dispatcher: ExperimentalCoroutineDispatcher = ExperimentalCoroutineDispatcher()
    private val observedThreads = ConcurrentHashMap<Thread, MutableSet<Int>>()
    private val tasksNum = 1_000_000
    private val processed = AtomicInteger(0)
    private val finishLatch = CountDownLatch(1)

    @After
    fun tearDown() {
        dispatcher.close()
    }

    @Test
    fun testExternalTasksSubmission() {
        stressTest(CommonPool)
    }

    @Test
    fun testInternalTasksSubmission() {
        stressTest(dispatcher)
    }

    @Test
    fun testStealingFromBlocking() {
        /*
         * Work-stealing stress test,
         * one thread submits pack of tasks, waits until they are completed (to avoid work offloading)
         * and then repeats, thus never executing its own tasks and relying only on work stealing.
         */
        var blockingThread: Thread? = null
        dispatcher.dispatch(EmptyCoroutineContext, Runnable {
            // Submit million tasks
            blockingThread = Thread.currentThread()
            var submittedTasks = 0
            val processedCounter = AtomicLong(0)
            while (submittedTasks <= tasksNum) {
                for (i in 1..120) {
                    if (++submittedTasks > tasksNum) {
                        // Block current thread
                        finishLatch.await()
                        return@Runnable
                    }

                    val defensiveCopy = submittedTasks
                    dispatcher.dispatch(EmptyCoroutineContext, Runnable {
                        processTask(defensiveCopy)
                        processedCounter.incrementAndGet()
                    })
                }

                while (processedCounter.get() < 100) {
                    Thread.yield()
                }
                processedCounter.set(0L)
            }
        })

        finishLatch.await()

        require(blockingThread!! !in observedThreads)
        require(observedThreads.size == Runtime.getRuntime().availableProcessors() - 1)
        validateResults()
    }

    private fun stressTest(submissionInitiator: CoroutineDispatcher) {
        /*
         * Run 1 million tasks and validate that
         * 1) All of them are completed successfully
         * 2) Every thread executed task at least once
         */
        submissionInitiator.dispatch(EmptyCoroutineContext, Runnable {
            for (i in 1..tasksNum) {
                dispatcher.dispatch(EmptyCoroutineContext, Runnable {
                    processTask(i)
                })
            }
        })

        finishLatch.await()
        assertEquals(Runtime.getRuntime().availableProcessors(), observedThreads.size)
        validateResults()
    }

    private fun processTask(i: Int) {
        var numbers = observedThreads[Thread.currentThread()]
        if (numbers == null) {
            numbers = hashSetOf()
            observedThreads[Thread.currentThread()] = numbers
        }

        require(numbers.add(i))

        if (processed.incrementAndGet() == tasksNum) {
            finishLatch.countDown()
        }
    }

    private fun validateResults() {
        val result = observedThreads.values.flatMap { it }.toSet()
        assertEquals((1..tasksNum).toSet(), result)
    }

}
