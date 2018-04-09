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
        (1L..4L).forEach { queue.add(task(it), globalQueue) }
        assertEquals(listOf(4L, 1L, 2L, 3L), queue.drain())
    }

    @Test
    fun testWorkOffload() {
        val queue = WorkQueue()
        val globalQueue = ArrayDeque<Task>()
        (1L..130L).forEach { queue.add(task(it), globalQueue) }

        val expectedLocalResults = (64L..129L).toMutableList()
        expectedLocalResults.add(0, 130L)
        assertEquals(expectedLocalResults, queue.drain())
        assertEquals((1L..63L).toList(), globalQueue.map { (it as Task).submissionTime }.toList())
    }

    @Test
    fun testWorkOffloadPrecision() {
        val queue = WorkQueue()
        val globalQueue = ArrayDeque<Task>()
        repeat(128) { require(queue.add(task(0), globalQueue)) }
        require(globalQueue.isEmpty())
        require(!queue.add(task(0), globalQueue))
        require(globalQueue.size == 63)
    }

    @Test
    fun testTimelyStealing() {
        val victim = WorkQueue()
        val globalQueue = ArrayDeque<Task>()

        (1L..96L).forEach { victim.add(task(it), globalQueue) }

        timeSource.step()
        timeSource.step(2)

        val stealer = WorkQueue()
        require(stealer.trySteal(victim, globalQueue))
        assertEquals(arrayListOf(2L, 1L), stealer.drain())

        require(!stealer.trySteal(victim, globalQueue))
        assertEquals(emptyList(), stealer.drain())

        timeSource.step(3)
        require(stealer.trySteal(victim, globalQueue))
        assertEquals(arrayListOf(5L, 3L, 4L), stealer.drain())
        require(globalQueue.isEmpty())
        assertEquals((6L..96L).toSet(), victim.drain().toSet())
    }

    @Test
    fun testStealingBySize() {
        val victim = WorkQueue()
        val globalQueue = ArrayDeque<Task>()

        (1L..110L).forEach { victim.add(task(it), globalQueue) }
        val stealer = WorkQueue()
        require(stealer.trySteal(victim, globalQueue))
        assertEquals((1L..13L).toSet(), stealer.drain().toSet())

        require(!stealer.trySteal(victim, globalQueue))
        require(stealer.drain().isEmpty())


        timeSource.step()
        timeSource.step(13)
        require(!stealer.trySteal(victim, globalQueue))
        require(stealer.drain().isEmpty())

        timeSource.step(1)
        require(stealer.trySteal(victim, globalQueue))
        assertEquals(arrayListOf(14L), stealer.drain())

    }

    @Test
    fun testStealingFromHead() {
        val victim = WorkQueue()
        val globalQueue = ArrayDeque<Task>()
        (1L..2L).forEach { victim.add(task(it), globalQueue) }
        timeSource.step()
        timeSource.step(3)

        val stealer = WorkQueue()
        require(stealer.trySteal(victim, globalQueue))
        assertEquals(arrayListOf(1L), stealer.drain())

        require(stealer.trySteal(victim, globalQueue))
        assertEquals(arrayListOf(2L), stealer.drain())
    }
}

internal fun task(n: Long) = TimedTask(Runnable {}, n, TaskMode.NON_BLOCKING)

internal fun WorkQueue.drain(): List<Long> {
    var task: Task? = poll()
    val result = arrayListOf<Long>()
    while (task != null) {
        result += task.submissionTime
        task = poll()
    }

    return result
}
