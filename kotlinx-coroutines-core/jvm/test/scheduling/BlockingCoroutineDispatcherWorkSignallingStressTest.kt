/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("DeferredResultUnused")

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class BlockingCoroutineDispatcherWorkSignallingStressTest : SchedulerTestBase() {

    @Test
    fun testCpuTasksStarvation() = runBlocking {
        val iterations = 1000 * stressTestMultiplier
        repeat(iterations) {
            // Create a dispatcher every iteration to increase probability of race
            val dispatcher = SchedulerCoroutineDispatcher(CORES_COUNT)
            val blockingDispatcher = dispatcher.blocking(100)

            val blockingBarrier = CyclicBarrier(CORES_COUNT * 3 + 1)
            val cpuBarrier = CyclicBarrier(CORES_COUNT + 1)

            val cpuTasks = CopyOnWriteArrayList<Deferred<*>>()
            val blockingTasks = CopyOnWriteArrayList<Deferred<*>>()

            repeat(CORES_COUNT) {
                async(dispatcher) {
                    // These two will be stolen first
                    blockingTasks += blockingAwait(blockingDispatcher, blockingBarrier)
                    blockingTasks += blockingAwait(blockingDispatcher, blockingBarrier)
                    // Empty on CPU job which should be executed while blocked tasks are waiting
                    cpuTasks += cpuAwait(dispatcher, cpuBarrier)
                    // Block with next task. Block cores * 3 threads in total
                    blockingTasks += blockingAwait(blockingDispatcher, blockingBarrier)
                }
            }

            cpuTasks.forEach { require(it.isActive) }
            cpuBarrier.await()
            cpuTasks.awaitAll()
            blockingTasks.forEach { require(it.isActive) }
            blockingBarrier.await()
            blockingTasks.awaitAll()
            dispatcher.close()
        }
    }

    private fun CoroutineScope.blockingAwait(
        blockingDispatcher: CoroutineDispatcher,
        blockingBarrier: CyclicBarrier
    ) = async(blockingDispatcher) { blockingBarrier.await() }


    private fun CoroutineScope.cpuAwait(
        blockingDispatcher: CoroutineDispatcher,
        blockingBarrier: CyclicBarrier
    ) = async(blockingDispatcher) { blockingBarrier.await() }

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
            tasks.forEach { assertTrue(it.isActive) }
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
            tasks.forEach { assertTrue(it.isActive) }
            barrier.await()
            tasks.joinAll()
            cpuTasks.forEach { it.cancelAndJoin() }
        }
    }
}
