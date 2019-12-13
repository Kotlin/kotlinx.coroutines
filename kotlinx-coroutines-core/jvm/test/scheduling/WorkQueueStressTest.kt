/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.concurrent.*
import kotlin.test.*

class WorkQueueStressTest : TestBase() {

    private val threads = mutableListOf<Thread>()
    private val offerIterations = 100_000 * stressTestMultiplierSqrt // memory pressure, not CPU time
    private val stealersCount = 6
    private val stolenTasks = Array(stealersCount) { GlobalQueue() }
    private val globalQueue = GlobalQueue() // only producer will use it
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
                while (producerQueue.bufferSize > BUFFER_CAPACITY / 2) {
                    Thread.yield()
                }

                producerQueue.add(task(i.toLong()))?.let { globalQueue.addLast(it) }
            }

            producerFinished = true
        }

        for (i in 0 until stealersCount) {
            threads += thread(name = "stealer $i") {
                val myQueue = WorkQueue()
                startLatch.await()
                while (!producerFinished || producerQueue.size != 0) {
                    stolenTasks[i].addAll(myQueue.drain().map { task(it) })
                    myQueue.tryStealFrom(victim = producerQueue)
                }

                // Drain last element which is not counted in buffer
                stolenTasks[i].addAll(myQueue.drain().map { task(it) })
                myQueue.tryStealFrom(producerQueue)
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
        threads += thread(name = "producer") {
            startLatch.await()
            for (i in 1..offerIterations) {
                while (producerQueue.bufferSize == BUFFER_CAPACITY - 1) {
                    Thread.yield()
                }

                // No offloading to global queue here
                producerQueue.add(task(i.toLong()))
            }
        }

        val stolen = GlobalQueue()
        threads += thread(name = "stealer") {
            val myQueue = WorkQueue()
            startLatch.await()
            while (stolen.size != offerIterations) {
                if (myQueue.tryStealFrom(producerQueue) != NOTHING_TO_STEAL) {
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
            assertEquals(stolenTask.size, stolenTask.map { it }.toSet().size)
            result += stolenTask.map { it.submissionTime }
        }

        result += globalQueue.map { it.submissionTime }
        val expected = (1L..offerIterations).toSet()
        assertEquals(expected, result, "Following elements are missing: ${(expected - result)}")
    }

    private fun GlobalQueue.addAll(tasks: Collection<Task>) {
        tasks.forEach { addLast(it) }
    }
}
