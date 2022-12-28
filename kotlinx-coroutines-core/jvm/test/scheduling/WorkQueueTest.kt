/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.jvm.internal.Ref.ObjectRef
import kotlin.test.*

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
        (1L..4L).forEach { queue.add(task(it)) }
        assertEquals(listOf(4L, 1L, 2L, 3L), queue.drain(ObjectRef()))
    }

    @Test
    fun testAddWithOffload() {
        val queue = WorkQueue()
        val size = 130L
        val offload = GlobalQueue()
        (0 until size).forEach { queue.add(task(it))?.let { t -> offload.addLast(t) } }

        val expectedResult = listOf(129L) + (0L..126L).toList()
        val actualResult = queue.drain(ObjectRef())
        assertEquals(expectedResult, actualResult)
        assertEquals((0L until size).toSet().minus(expectedResult.toSet()), offload.drain().toSet())
    }

    @Test
    fun testWorkOffloadPrecision() {
        val queue = WorkQueue()
        val globalQueue = GlobalQueue()
        repeat(128) { assertNull(queue.add(task(it.toLong()))) }
        assertTrue(globalQueue.isEmpty)
        assertEquals(127L, queue.add(task(0))?.submissionTime)
    }

    @Test
    fun testStealingFromHead() {
        val victim = WorkQueue()
        victim.add(task(1L))
        victim.add(task(2L))
        timeSource.step()
        timeSource.step(3)

        val stealer = WorkQueue()
        val ref = ObjectRef<Task?>()
        assertEquals(TASK_STOLEN, victim.trySteal(ref))
        assertEquals(arrayListOf(1L), stealer.drain(ref))

        assertEquals(TASK_STOLEN, victim.trySteal(ref))
        assertEquals(arrayListOf(2L), stealer.drain(ref))
    }

    @Test
    fun testPollBlocking() {
        val queue = WorkQueue()
        assertNull(queue.pollBlocking())
        val blockingTask = blockingTask(1L)
        queue.add(blockingTask)
        queue.add(task(1L))
        assertSame(blockingTask, queue.pollBlocking())
    }
}

internal fun task(n: Long) = TaskImpl(Runnable {}, n, NonBlockingContext)
internal fun blockingTask(n: Long) = TaskImpl(Runnable {}, n, BlockingContext)

internal fun WorkQueue.drain(ref: ObjectRef<Task?>): List<Long> {
    var task: Task? = poll()
    val result = arrayListOf<Long>()
    while (task != null) {
        result += task.submissionTime
        task = poll()
    }
    if (ref.element != null) {
        result += ref.element!!.submissionTime
        ref.element = null
    }
    return result
}

internal fun GlobalQueue.drain(): List<Long> {
    var task: Task? = removeFirstOrNull()
    val result = arrayListOf<Long>()
    while (task != null) {
        result += task.submissionTime
        task = removeFirstOrNull()
    }
    return result
}
