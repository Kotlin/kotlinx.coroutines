/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.AVAILABLE_PROCESSORS
import org.junit.Test
import java.util.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.CountDownLatch
import java.util.concurrent.CyclicBarrier
import java.util.concurrent.atomic.AtomicInteger
import kotlin.random.*
import kotlin.random.Random
import kotlin.test.*
import kotlin.time.*

class CoroutineSchedulerInternalApiStressTest : TestBase() {

    @Test(timeout = 120_000L)
    fun testHelpDefaultIoIsIsolated() = repeat(100 * stressTestMultiplierSqrt) {
        val ioTaskMarker = ThreadLocal.withInitial { false }
        runTest {
            val jobToComplete = Job()
            val expectedIterations = 100
            val completionLatch = CountDownLatch(1)
            val tasksToCompleteJob = AtomicInteger(expectedIterations)
            val observedIoThreads = Collections.newSetFromMap(ConcurrentHashMap<Thread, Boolean>())
            val observedDefaultThreads = Collections.newSetFromMap(ConcurrentHashMap<Thread, Boolean>())

            val barrier = CyclicBarrier(AVAILABLE_PROCESSORS)
            val spawners = ArrayList<Job>()
            repeat(AVAILABLE_PROCESSORS - 1) {
                // Launch CORES - 1 spawners
                spawners += launch(Dispatchers.Default) {
                    barrier.await()
                    repeat(expectedIterations) {
                        launch {
                            val tasksLeft = tasksToCompleteJob.decrementAndGet()
                            if (tasksLeft < 0) return@launch // Leftovers are being executed all over the place
                            observedDefaultThreads.add(Thread.currentThread())
                            if (tasksLeft == 0) {
                                // Verify threads first
                                try {
                                    assertFalse(observedIoThreads.containsAll(observedDefaultThreads))
                                } finally {
                                    jobToComplete.complete()
                                }
                            }
                        }

                        // Sometimes launch an IO task to mess with a scheduler
                        if (Random.nextInt(0..9) == 0) {
                            launch(Dispatchers.IO) {
                                ioTaskMarker.set(true)
                                observedIoThreads.add(Thread.currentThread())
                                assertTrue(Thread.currentThread().isIoDispatcherThread())
                            }
                        }
                    }
                    completionLatch.await()
                }
            }

            withContext(Dispatchers.Default) {
                barrier.await()
                var timesHelped = 0
                while (!jobToComplete.isCompleted) {
                    val result = runSingleTaskFromCurrentSystemDispatcher()
                    assertFalse(ioTaskMarker.get())
                    if (result == 0L) {
                        ++timesHelped
                        continue
                    } else if (result >= 0L) {
                        Thread.sleep(result.toDuration(DurationUnit.NANOSECONDS).toDelayMillis())
                    } else {
                        Thread.sleep(10)
                    }
                }
                completionLatch.countDown()
//                assertEquals(100, timesHelped)
//                assertTrue(Thread.currentThread() in observedDefaultThreads, observedDefaultThreads.toString())
            }
        }
    }
}

