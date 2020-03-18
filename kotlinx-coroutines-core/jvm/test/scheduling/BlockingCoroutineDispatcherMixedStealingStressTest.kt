/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.*
import java.util.concurrent.*

/**
 * Specific test that was designed to expose inference between stealing/polling of blocking and non-blocking tasks.RunningThreadStackMergeTest
 */
class BlockingCoroutineDispatcherMixedStealingStressTest : SchedulerTestBase() {

    private val iterations = 10_000

    @Before
    fun setUp() {
        idleWorkerKeepAliveNs = Long.MAX_VALUE
    }

    @Test
    fun testBlockingProgressPreventedInternal()  {
        val blocking = blockingDispatcher(corePoolSize).asExecutor()
        val regular = dispatcher.asExecutor()
        repeat(iterations * stressTestMultiplier) {
            val cpuBlocker = CyclicBarrier(corePoolSize + 1)
            val blockingBlocker = CyclicBarrier(2)
            regular.execute(Runnable {
                // Block all CPU cores except current one
                repeat(corePoolSize - 1) {
                    regular.execute(Runnable {
                        cpuBlocker.await()
                    })
                }

                blocking.execute(Runnable {
                    blockingBlocker.await()
                })

                regular.execute(Runnable {
                    blockingBlocker.await()
                    cpuBlocker.await()
                })
            })
            cpuBlocker.await()
        }
    }

    @Test
    fun testBlockingProgressPreventedExternal()  {
        val blocking = blockingDispatcher(corePoolSize).asExecutor()
        val regular = dispatcher.asExecutor()
        repeat(iterations / 2 * stressTestMultiplier) {
            val cpuBlocker = CyclicBarrier(corePoolSize + 1)
            val blockingBlocker = CyclicBarrier(2)
            repeat(corePoolSize) {
                regular.execute(Runnable {
                    cpuBlocker.await()
                })
            }
            // Wait for all threads to park
            while (true) {
                val waiters = Thread.getAllStackTraces().keys.count { (it.state == Thread.State.TIMED_WAITING || it.state == Thread.State.WAITING)
                        && it is CoroutineScheduler.Worker }
                if (waiters >= corePoolSize) break
                Thread.yield()
            }
            blocking.execute(Runnable {
                blockingBlocker.await()
            })
            regular.execute(Runnable {
            })

            blockingBlocker.await()
            cpuBlocker.await()
        }
    }
}