package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.TestBase
import org.junit.After
import org.junit.Before
import org.junit.Test
import java.util.*
import java.util.concurrent.CountDownLatch
import java.util.concurrent.SynchronousQueue
import kotlin.concurrent.thread
import kotlin.test.assertEquals

class WorkQueueStressTest : TestBase() {

    private val threads = mutableListOf<Thread>()
    private val offerIterations = 2_000_000
    private val stealersCount = 6
    private val stolenTasks = Array(stealersCount) { ArrayDeque<TimedTask>() }
    private val globalQueue = ArrayDeque<Task>() // only producer will use it
    private val producerQueue = WorkQueue()

    @Volatile
    private var producerFinished = false

    @Before
    fun setUp() {
        schedulerTimeSource = TestTimeSource(Long.MAX_VALUE) // always steal
    }

    @After
    fun tearDown() {
        schedulerTimeSource = NanoTimeSource
    }

    @Test
    fun testStealing() {
        val startLatch = CountDownLatch(1)

        threads += thread(name = "producer") {
            startLatch.await()
            for (i in 1..offerIterations) {
                while (producerQueue.bufferSize == BUFFER_CAPACITY - 1) {
                    Thread.yield()
                }

                producerQueue.offer(task(i.toLong()), globalQueue)
            }

            producerFinished = true
        }

        for (i in 0 until stealersCount) {
            threads += thread(name = "stealer $i") {
                val myQueue = WorkQueue()
                startLatch.await()
                while (!producerFinished || producerQueue.bufferSize != 0) {
                    producerQueue.offloadWork(true, { myQueue.offer(it, stolenTasks[i]) })
                }

                // Drain last element which is not counted in buffer
                producerQueue.offloadWork(true, { myQueue.offer(it, stolenTasks[i]) })
                stolenTasks[i].addAll(myQueue.drain().map { task(it) })
            }
        }

        startLatch.countDown()
        threads.forEach { it.join() }
        validate()
    }

    @Test
    fun testSingleProducerSingleStealer() {
        val startLatch = CountDownLatch(1)
        val fakeQueue = SynchronousQueue<Task>()
        threads += thread(name = "producer") {
            startLatch.await()
            for (i in 1..offerIterations) {
                while (producerQueue.bufferSize == BUFFER_CAPACITY - 1) {
                    Thread.yield()
                }

                // No offloading to global queue here
                producerQueue.offer(task(i.toLong()), fakeQueue)
            }
        }

        val stolen = ArrayDeque<Task>()
        threads += thread(name = "stealer") {
            val myQueue = WorkQueue()
            startLatch.await()
            var consumed = 0
            while (consumed != offerIterations) {
                producerQueue.offloadWork(true, {
                    ++consumed
                    myQueue.offer(it, stolen) })
            }
            stolen.addAll(myQueue.drain().map { task(it) })
        }

        startLatch.countDown()
        threads.forEach { it.join() }
        assertEquals((1L..offerIterations).toSet(), stolen.map { it.submissionTime }.toSet())
    }

    private fun validate() {
        val result = mutableSetOf<Long>()
        for (stolenTask in stolenTasks) {
            require(stolenTask.isNotEmpty())
            assertEquals(stolenTask.size, stolenTask.toSet().size)
            result += stolenTask.map { it.submissionTime }
        }

        result += globalQueue.map { it.submissionTime }
        val expected = (1L..offerIterations).toSet()
        assertEquals(expected, result, "Following elements are missing: ${(expected - result)}")
    }
}
