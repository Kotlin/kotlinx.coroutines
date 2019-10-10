/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
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
        assertEquals(listOf(4L, 1L, 2L, 3L), queue.drain())
    }

    @Test
    fun testAddWithOffload() {
        val queue = WorkQueue()
        val size = 130L
        val offload = GlobalQueue()
        (0 until size).forEach { queue.add(task(it))?.let { t -> offload.addLast(t) } }

        val expectedResult = listOf(129L) + (0L..126L).toList()
        val actualResult = queue.drain()
        assertEquals(expectedResult, actualResult)
        assertEquals((0L until size).toSet().minus(expectedResult), offload.drain().toSet())
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
        assertEquals(TASK_STOLEN, stealer.tryStealFrom(victim))
        assertEquals(arrayListOf(1L), stealer.drain())

        assertEquals(TASK_STOLEN, stealer.tryStealFrom(victim))
        assertEquals(arrayListOf(2L), stealer.drain())
    }
}

internal fun GlobalQueue.asTimeList(): List<Long> {
    val result = mutableListOf<Long>()
    var next = removeFirstOrNull()
    while (next != null) {
        result += next.submissionTime
        next = removeFirstOrNull()
    }

    return result
}

internal fun task(n: Long) = TaskImpl(Runnable {}, n, NonBlockingContext)

internal fun WorkQueue.drain(): List<Long> {
    var task: Task? = poll()
    val result = arrayListOf<Long>()
    while (task != null) {
        result += task.submissionTime
        task = poll()
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
