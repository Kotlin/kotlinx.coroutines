/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.Test
import java.lang.Runnable
import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

class CoroutineSchedulerTest : TestBase() {

    @Test
    fun testModesExternalSubmission() { // Smoke
        CoroutineScheduler(1, 1).use {
            for (mode in TaskMode.values()) {
                val latch = CountDownLatch(1)
                it.dispatch(Runnable {
                    latch.countDown()
                }, TaskContextImpl(mode))

                latch.await()
            }
        }
    }

    @Test
    fun testModesInternalSubmission() { // Smoke
        CoroutineScheduler(2, 2).use {
            val latch = CountDownLatch(TaskMode.values().size)
            it.dispatch(Runnable {
                for (mode in TaskMode.values()) {
                    it.dispatch(Runnable {
                        latch.countDown()
                    }, TaskContextImpl(mode))
                }
            })

            latch.await()
        }
    }

    @Test
    fun testNonFairSubmission() {
        CoroutineScheduler(1, 1).use {
            val startLatch = CountDownLatch(1)
            val finishLatch = CountDownLatch(2)

            it.dispatch(Runnable {
                it.dispatch(Runnable {
                    expect(2)
                    finishLatch.countDown()
                })

                it.dispatch(Runnable {
                    expect(1)
                    finishLatch.countDown()
                })
            })

            startLatch.countDown()
            finishLatch.await()
            finish(3)
        }
    }

    @Test
    fun testFairSubmission() {
        CoroutineScheduler(1, 1).use {
            val startLatch = CountDownLatch(1)
            val finishLatch = CountDownLatch(2)

            it.dispatch(Runnable {
                it.dispatch(Runnable {
                    expect(1)
                    finishLatch.countDown()
                })

                it.dispatch(Runnable {
                    expect(2)
                    finishLatch.countDown()
                }, fair = true)
            })

            startLatch.countDown()
            finishLatch.await()
            finish(3)
        }
    }

    @Test
    fun testRngUniformDistribution() {
        CoroutineScheduler(1, 128).use { scheduler ->
            val worker = scheduler.Worker(1)
            testUniformDistribution(worker, 2)
            testUniformDistribution(worker, 4)
            testUniformDistribution(worker, 8)
            testUniformDistribution(worker, 12)
            testUniformDistribution(worker, 16)
        }
    }

    @Test(expected = IllegalArgumentException::class)
    fun testNegativeCorePoolSize() {
        ExperimentalCoroutineDispatcher(-1, 4)
    }

    @Test(expected = IllegalArgumentException::class)
    fun testNegativeMaxPoolSize() {
        ExperimentalCoroutineDispatcher(1, -4)
    }

    @Test(expected = IllegalArgumentException::class)
    fun testCorePoolSizeGreaterThanMaxPoolSize() {
        ExperimentalCoroutineDispatcher(4, 1)
    }

    @Test
    fun testSelfClose() {
        val dispatcher = ExperimentalCoroutineDispatcher(1, 1)
        val latch = CountDownLatch(1)
        dispatcher.dispatch(EmptyCoroutineContext, Runnable {
            dispatcher.close(); latch.countDown()
        })
        latch.await()
    }

    @Test
    fun testInterruptionCleanup() {
        ExperimentalCoroutineDispatcher(1, 1).use {
            val executor = it.executor
            var latch = CountDownLatch(1)
            executor.execute {
                Thread.currentThread().interrupt()
                latch.countDown()
            }
            latch.await()
            Thread.sleep(100) // I am really sorry
            latch = CountDownLatch(1)
            executor.execute {
                try {
                    assertFalse(Thread.currentThread().isInterrupted)
                } finally {
                    latch.countDown()
                }
            }
            latch.await()
        }
    }

    private fun testUniformDistribution(worker: CoroutineScheduler.Worker, bound: Int) {
        val result = IntArray(bound)
        val iterations = 10_000_000
        repeat(iterations) {
            ++result[worker.nextInt(bound)]
        }

        val bucketSize = iterations / bound
        for (i in result) {
            val ratio = i.toDouble() / bucketSize
            // 10% deviation
            check(ratio <= 1.1)
            check(ratio >= 0.9)
        }
    }

    private class TaskContextImpl(override val taskMode: TaskMode) : TaskContext {
        override fun afterTask() {}
    }
}