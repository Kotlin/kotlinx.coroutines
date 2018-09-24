/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.scheduling

import kotlinx.coroutines.experimental.*
import org.junit.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

@Ignore // these tests are too unstable on Windows, should be virtualized
class CoroutineSchedulerShrinkTest : SchedulerTestBase() {

    private val blockingTasksCount = CORES_COUNT * 3
    private val blockingTasksBarrier = CyclicBarrier(blockingTasksCount + 1)
    lateinit var blocking: CoroutineContext

    @Before
    fun setUp() {
        corePoolSize = CORES_COUNT
        // shutdown after 100ms
        idleWorkerKeepAliveNs = TimeUnit.MILLISECONDS.toNanos(100)
        blocking = blockingDispatcher(100)
    }

    @Test(timeout = 10_000)
    fun testShrinkOnlyBlockingTasks() = runBlocking {
        // Init dispatcher
        async(dispatcher) { }.await()
        // Pool is initialized with core size in the beginning
        checkPoolThreadsExist(1..2)

        // Run blocking tasks and check increased threads count
        val blockingTasks = launchBlocking()
        checkBlockingTasks(blockingTasks)

        delay(2000)
        // Pool should shrink to core size +- eps
        checkPoolThreadsExist(CORES_COUNT..CORES_COUNT + 3)
    }

    @Test(timeout = 10_000)
    fun testShrinkMixedWithWorkload() = runBlocking {
        // Block blockingTasksCount cores in blocking dispatcher
        val blockingTasks = launchBlocking()

        // Block cores count CPU threads
        val nonBlockingBarrier = CyclicBarrier(CORES_COUNT + 1)
        val nonBlockingTasks = (1..CORES_COUNT).map {
            async(dispatcher) {
                nonBlockingBarrier.await()
            }
        }

        // Check CPU tasks succeeded properly even though blocking tasks acquired everything
        nonBlockingTasks.forEach { require(it.isActive) }
        nonBlockingBarrier.await()
        nonBlockingTasks.joinAll()

        // Check blocking tasks succeeded properly
        checkBlockingTasks(blockingTasks)

        delay(2000)
        // Pool should shrink to core size
        checkPoolThreadsExist(CORES_COUNT..CORES_COUNT + 3)
    }

    private suspend fun checkBlockingTasks(blockingTasks: List<Deferred<*>>) {
        checkPoolThreadsExist(blockingTasksCount..corePoolSize + blockingTasksCount)
        blockingTasksBarrier.await()
        blockingTasks.joinAll()
    }

    @Test(timeout = 10_000)
    fun testShrinkWithExternalTasks() = runBlocking {
        val nonBlockingBarrier = CyclicBarrier(CORES_COUNT + 1)
        val blockingTasks = launchBlocking()

        val nonBlockingTasks = (1..CORES_COUNT).map {
            async(dispatcher) {
                nonBlockingBarrier.await()
            }
        }

        // Tasks that burn CPU. Delay is important so tasks will be scheduled from external thread
        val busySpinTasks = (1..2).map {
            async(dispatcher) {
                while (true) {
                    delay(100, TimeUnit.MICROSECONDS)
                    yield()
                }
            }
        }

        nonBlockingTasks.forEach { require(it.isActive) }
        nonBlockingBarrier.await()
        nonBlockingTasks.joinAll()

        checkBlockingTasks(blockingTasks)

        delay(2000)
        // Pool should shrink almost to core size (+/- eps)
        checkPoolThreadsExist(CORES_COUNT..CORES_COUNT + 3)

        busySpinTasks.forEach {
            require(it.isActive)
            it.cancelAndJoin()
        }
    }

    private suspend fun launchBlocking(): List<Deferred<*>> {
        val result = (1..blockingTasksCount).map {
            GlobalScope.async(blocking) {
                blockingTasksBarrier.await()
            }
        }

        while (blockingTasksBarrier.numberWaiting != blockingTasksCount) {
            delay(1)
        }

        return result
    }
}
