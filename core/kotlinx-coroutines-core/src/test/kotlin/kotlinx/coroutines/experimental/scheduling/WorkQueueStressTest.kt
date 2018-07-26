package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.*
import org.junit.*
import org.junit.Test
import java.util.*
import java.util.concurrent.*
import kotlin.concurrent.*
import kotlin.test.*

class WorkQueueStressTest : TestBase() {

    private val threads = mutableListOf<Thread>()
    private val offerIterations = 100_000 * stressTestMultiplierSqrt // memory pressure, not CPU time
    private val stealersCount = 6
    private val stolenTasks = Array(stealersCount) { Queue() }
    private val globalQueue = Queue() // only producer will use it
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

                producerQueue.add(task(i.toLong()), globalQueue)
            }

            producerFinished = true
        }

        for (i in 0 until stealersCount) {
            threads += thread(name = "stealer $i") {
                val myQueue = WorkQueue()
                startLatch.await()
                while (!producerFinished || producerQueue.bufferSize != 0) {
                    myQueue.trySteal(producerQueue, stolenTasks[i])
                }

                // Drain last element which is not counted in buffer
                myQueue.trySteal(producerQueue, stolenTasks[i])
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
        val fakeQueue = Queue()
        threads += thread(name = "producer") {
            startLatch.await()
            for (i in 1..offerIterations) {
                while (producerQueue.bufferSize == BUFFER_CAPACITY - 1) {
                    Thread.yield()
                }

                // No offloading to global queue here
                producerQueue.add(task(i.toLong()), fakeQueue)
            }
        }

        val stolen = Queue()
        threads += thread(name = "stealer") {
            val myQueue = WorkQueue()
            startLatch.await()
            while (stolen.size != offerIterations) {
                if (!myQueue.trySteal(producerQueue, stolen)) {
                    stolen.addAll(myQueue.drain().map { task(it) })
                }
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
            require(!stolenTask.isEmpty())
            assertEquals(stolenTask.size, stolenTask.size)
            result += stolenTask.map { it.submissionTime }
        }

        result += globalQueue.map { it.submissionTime }
        val expected = (1L..offerIterations).toSet()
        assertEquals(expected, result, "Following elements are missing: ${(expected - result)}")
    }
}

internal class Queue : GlobalQueue() {
    override fun removeFirstBlockingModeOrNull(): Task? = error("Should not be called")

    fun addAll(tasks: Collection<Task>) {
        tasks.forEach { addLast(it) }
    }

    fun <R> map(transform: (Task) -> R): List<R> {
        val result = ArrayList<R>()
        fold(Unit) { _, task -> result.add(transform(task)) }
        return result
    }
}
