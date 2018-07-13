/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("DeferredResultUnused")

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.*
import java.util.concurrent.*
import java.util.concurrent.atomic.*

class BlockingCoroutineDispatcherStressTest : SchedulerTestBase() {

    init {
        corePoolSize = CORES_COUNT
    }

    private val observedConcurrency = ConcurrentHashMap<Int, Boolean>()
    private val concurrentWorkers = AtomicInteger(0)

    @Test
    fun testLimitParallelism() = runBlocking {
        val limitingDispatcher = blockingDispatcher(CORES_COUNT)
        val iterations = 50_000 * stressTestMultiplier
        val tasks = (1..iterations).map {
            async(limitingDispatcher) {
                try {
                    val currentlyExecuting = concurrentWorkers.incrementAndGet()
                    observedConcurrency[currentlyExecuting] = true
                    require(currentlyExecuting <= CORES_COUNT)
                } finally {
                    concurrentWorkers.decrementAndGet()
                }
            }
        }

        tasks.forEach { it.await() }
        require(tasks.isNotEmpty())
        for (i in CORES_COUNT + 1..CORES_COUNT * 2) {
            require(i !in observedConcurrency.keys) { "Unexpected state: $observedConcurrency" }
        }

        checkPoolThreadsCreated(CORES_COUNT..CORES_COUNT + CORES_COUNT * 2)
    }

    @Test
    fun testCpuTasksStarvation() = runBlocking {
        val iterations = 1000 * stressTestMultiplier

        repeat(iterations) {
            // Create new dispatcher every iteration to increase probability of race
            val dispatcher = ExperimentalCoroutineDispatcher(CORES_COUNT)
            val blockingDispatcher = dispatcher.blocking(100)

            val blockingBarrier = CyclicBarrier(CORES_COUNT * 3 + 1)
            val cpuBarrier = CyclicBarrier(CORES_COUNT + 1)

            val cpuTasks = CopyOnWriteArrayList<Deferred<*>>()
            val blockingTasks = CopyOnWriteArrayList<Deferred<*>>()

            repeat(CORES_COUNT) {
                async(dispatcher) {
                    // These two will be stolen first
                    blockingTasks += async(blockingDispatcher) { blockingBarrier.await() }
                    blockingTasks += async(blockingDispatcher) { blockingBarrier.await() }


                    // Empty on CPU job which should be executed while blocked tasks are hang
                    cpuTasks += async(dispatcher) { cpuBarrier.await() }

                    // Block with next task. Block cores * 3 threads in total
                    blockingTasks += async(blockingDispatcher) { blockingBarrier.await() }
                }
            }

            cpuTasks.forEach { require(it.isActive) }
            cpuBarrier.await()
            cpuTasks.forEach { it.await() }
            blockingTasks.forEach { require(it.isActive) }
            blockingBarrier.await()
            blockingTasks.forEach { it.await() }
            dispatcher.close()
        }
    }

    @Test
    fun testBlockingTasksStarvation() = runBlocking {
        corePoolSize = 2 // Easier to reproduce race with unparks
        val iterations = 10_000 * stressTestMultiplier
        val blockingLimit = 4 // CORES_COUNT * 3
        val blocking = blockingDispatcher(blockingLimit)

        repeat(iterations) {
            val barrier = CyclicBarrier(blockingLimit + 1)
            // Should eat all limit * 3 cpu without any starvation
            val tasks = (1..blockingLimit).map { async(blocking) { barrier.await() } }

            tasks.forEach { require(it.isActive) }
            barrier.await()
            tasks.joinAll()
        }
    }

    @Test
    fun testBlockingTasksStarvationWithCpuTasks() = runBlocking {
        val iterations = 1000 * stressTestMultiplier
        val blockingLimit = CORES_COUNT * 2
        val blocking = blockingDispatcher(blockingLimit)

        repeat(iterations) {
            // Overwhelm global queue with external CPU tasks
            val cpuTasks = (1..CORES_COUNT).map { async(dispatcher) { while (true) delay(1) } }

            val barrier = CyclicBarrier(blockingLimit + 1)
            // Should eat all limit * 3 cpu without any starvation
            val tasks = (1..blockingLimit).map { async(blocking) { barrier.await() } }

            tasks.forEach { require(it.isActive) }
            barrier.await()
            tasks.joinAll()
            cpuTasks.forEach { it.cancelAndJoin() }
        }
    }
}
