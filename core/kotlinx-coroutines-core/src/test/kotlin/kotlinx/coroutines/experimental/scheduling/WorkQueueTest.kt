package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.Runnable
import kotlinx.coroutines.experimental.TestBase
import org.junit.After
import org.junit.Before
import org.junit.Test
import java.util.*
import kotlin.test.assertEquals


class WorkQueueTest : TestBase() {

    private val timeSource = TestTimeSource(0)

    @Before
    fun setUp() {
        schedulerTimeSource = timeSource

    }

    @After
    fun tearDown() {
        schedulerTimeSource = NanoTimeSource
    }

    @Test
    fun testLastScheduledComesFirst() {
        val queue = WorkQueue()
        val globalQueue = ArrayDeque<Task>()
        (1L..4L).forEach { queue.offer(task(it), globalQueue) }
        assertEquals(listOf(4L, 1L, 2L, 3L), queue.drain())
    }

    @Test
    fun testWorkOffload() {
        val queue = WorkQueue()
        val globalQueue = ArrayDeque<Task>()
        (1L..130L).forEach { queue.offer(task(it), globalQueue) }

        val expectedLocalResults = (64L..129L).toMutableList()
        expectedLocalResults.add(0, 130L)
        assertEquals(expectedLocalResults, queue.drain())
        assertEquals((1L..63L).toList(), globalQueue.map { (it as Task).submissionTime }.toList())
    }

    @Test
    fun testTimelyWorkOffload() {
        val queue = WorkQueue()
        val globalQueue = ArrayDeque<Task>()

        (1L..128L).forEach { queue.offer(task(it), globalQueue) }

        timeSource.step()
        timeSource.step(2)

        val stealer = WorkQueue()
        queue.offloadWork(true, { stealer.offer(it, globalQueue) })
        assertEquals(arrayListOf(2L, 1L), stealer.drain())

        queue.offloadWork(true, { stealer.offer(it, globalQueue) })
        assertEquals(emptyList(), stealer.drain())

        timeSource.step(3)
        queue.offloadWork(true, { stealer.offer(it, globalQueue) })
        assertEquals(arrayListOf(5L, 3L, 4L), stealer.drain())
    }

    @Test
    fun testStealingFromHead() {
        val queue = WorkQueue()
        val globalQueue = ArrayDeque<Task>()
        (1L..2L).forEach { queue.offer(task(it), globalQueue) }
        timeSource.step()
        timeSource.step(3)

        val stealer = WorkQueue()
        queue.offloadWork(true, { stealer.offer(it, globalQueue) })
        assertEquals(arrayListOf(1L), stealer.drain())

        queue.offloadWork(true, { stealer.offer(it, globalQueue) })
        assertEquals(arrayListOf(2L), stealer.drain())
    }
}

internal fun task(n: Long) = TimedTask(n, Runnable {})

internal fun WorkQueue.drain(): List<Long> {
    var task: Task? = poll()
    val result = arrayListOf<Long>()
    while (task != null) {
        result += task.submissionTime
        task = poll()
    }

    return result
}
