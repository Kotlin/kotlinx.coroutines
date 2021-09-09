/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.*
import org.junit.rules.*
import java.util.concurrent.*

class BlockingCoroutineDispatcherTest : SchedulerTestBase() {

    @get:Rule
    val timeout = Timeout.seconds(10L)!!

    @Test
    fun testNonBlockingWithBlockingExternal() = runBlocking {
        val barrier = CyclicBarrier(2)

        val blockingJob = launch(blockingDispatcher.value) {
            barrier.await()
        }

        val nonBlockingJob = launch(dispatcher) {
            barrier.await()
        }

        nonBlockingJob.join()
        blockingJob.join()
        checkPoolThreadsCreated(2..3)
    }

    @Test
    fun testNonBlockingFromBlocking() = runBlocking {
        val barrier = CyclicBarrier(2)

        val blocking = launch(blockingDispatcher.value) {
            // This task will be stolen
            launch(dispatcher) {
                barrier.await()
            }

            barrier.await()
        }

        blocking.join()
        checkPoolThreadsCreated(2..3)
    }

    @Test
    fun testScheduleBlockingThreadCount() = runTest {
        // After first iteration pool is idle, repeat, no new threads should be created
        repeat(2) {
            val blocking = launch(blockingDispatcher.value) {
                launch(blockingDispatcher.value) {
                }
            }

            blocking.join()
            // Depends on how fast thread will be created
            checkPoolThreadsCreated(2..3)
        }
    }

    @Test
    fun testNoCpuStarvation() = runBlocking {
        val tasksNum = 100
        val barrier = CyclicBarrier(tasksNum + 1)
        val tasks = (1..tasksNum).map { launch(blockingDispatcher.value) { barrier.await() } }

        val cpuTask = launch(dispatcher) {
            // Do nothing, just complete
        }

        cpuTask.join()
        tasks.forEach { require(it.isActive) }
        barrier.await()
        tasks.joinAll()
    }

    @Test
    fun testNoCpuStarvationWithMultipleBlockingContexts() = runBlocking {
        val firstBarrier = CyclicBarrier(11)
        val secondBarrier = CyclicBarrier(11)
        val blockingDispatcher = blockingDispatcher(10)
        val blockingDispatcher2 = blockingDispatcher(10)

        val blockingTasks = (1..10).flatMap {
            listOf(launch(blockingDispatcher) { firstBarrier.await() }, launch(blockingDispatcher2) { secondBarrier.await() })
        }

        val cpuTasks = (1..100).map {
            launch(dispatcher) {
                // Do nothing, just complete
            }
        }.toList()

        cpuTasks.joinAll()
        blockingTasks.forEach { require(it.isActive) }
        firstBarrier.await()
        secondBarrier.await()
        blockingTasks.joinAll()
        checkPoolThreadsCreated(21 /* blocking tasks + 1 for CPU */..20 + CORES_COUNT)
    }

    @Test
    fun testNoExcessThreadsCreated() = runBlocking {
        corePoolSize = 4

        val tasksNum = 100
        val barrier = CyclicBarrier(tasksNum + 1)
        val blockingTasks = (1..tasksNum).map { launch(blockingDispatcher.value) { barrier.await() } }

        val nonBlockingTasks = (1..tasksNum).map {
            launch(dispatcher) {
                yield()
            }
        }

        nonBlockingTasks.joinAll()
        barrier.await()
        blockingTasks.joinAll()
        // There may be race when multiple CPU threads are trying to lazily created one more
        checkPoolThreadsCreated(101..100 + CORES_COUNT)
    }

    @Test
    fun testBlockingFairness() = runBlocking {
        corePoolSize = 1
        maxPoolSize = 1

        val blocking = blockingDispatcher(1)
        val task = async(dispatcher) {
            expect(1)

            val nonBlocking = async(dispatcher) {
                expect(3)
            }

            val firstBlocking = async(blocking) {
                expect(2)
            }

            val secondBlocking = async(blocking) {
                // Already have 1 queued blocking task, so this one wouldn't be scheduled to head
                expect(4)
            }

            listOf(firstBlocking, nonBlocking, secondBlocking).joinAll()
            finish(5)
        }

        task.await()
    }

    @Test
    fun testBoundedBlockingFairness() = runBlocking {
        corePoolSize = 1
        maxPoolSize = 1

        val blocking = blockingDispatcher(2)
        val task = async(dispatcher) {
            expect(1)

            val nonBlocking = async(dispatcher) {
                expect(3)
            }

            val firstBlocking = async(blocking) {
                expect(4)
            }

            val secondNonBlocking = async(dispatcher) {
                expect(5)
            }

            val secondBlocking = async(blocking) {
                expect(2) // <- last submitted blocking is executed first
            }

            val thirdBlocking = async(blocking) {
                expect(6) // parallelism level is reached before this task
            }

            listOf(firstBlocking, nonBlocking, secondBlocking, secondNonBlocking, thirdBlocking).joinAll()
            finish(7)
        }

        task.await()
    }

    @Test(timeout = 1_000)
    fun testYield() = runBlocking {
        corePoolSize = 1
        maxPoolSize = 1
        val bd = blockingDispatcher(1)
        val outerJob = launch(bd) {
            expect(1)
            val innerJob = launch(bd) {
                // Do nothing
                expect(3)
            }

            expect(2)
            while (innerJob.isActive) {
                yield()
            }

            expect(4)
            innerJob.join()
        }

        outerJob.join()
        finish(5)
    }

    @Test
    fun testUndispatchedYield() = runTest {
        expect(1)
        corePoolSize = 1
        maxPoolSize = 1
        val blockingDispatcher = blockingDispatcher(1)
        val job = launch(blockingDispatcher, CoroutineStart.UNDISPATCHED) {
            expect(2)
            yield()
        }
        expect(3)
        job.join()
        finish(4)
    }

    @Test(expected = IllegalArgumentException::class)
    fun testNegativeParallelism() {
        blockingDispatcher(-1)
    }

    @Test(expected = IllegalArgumentException::class)
    fun testZeroParallelism() {
        blockingDispatcher(0)
    }
}
