/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.AVAILABLE_PROCESSORS
import org.junit.Test
import java.util.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.CyclicBarrier
import java.util.concurrent.atomic.AtomicInteger
import kotlin.random.*
import kotlin.random.Random
import kotlin.test.*
import kotlin.time.*

class CoroutineSchedulerInternalApiStressTest : TestBase() {

    @Test
    fun testHelpDefaultIoIsIsolated() {
        repeat(10) {
            runTest {
                val jobToComplete = Job()
                val tasksToCompleteJob = AtomicInteger(200)

                val observedIoThreads = Collections.newSetFromMap(ConcurrentHashMap<Thread, Boolean>())
                val observedDefaultThreads = Collections.newSetFromMap(ConcurrentHashMap<Thread, Boolean>())

                val barrier = CyclicBarrier(AVAILABLE_PROCESSORS)
                repeat(AVAILABLE_PROCESSORS - 1) {
                    // Launch CORES - 1 spawners
                    launch(Dispatchers.Default) {
                        barrier.await()
                        while (!jobToComplete.isCompleted) {
                            launch {
                                observedDefaultThreads.add(Thread.currentThread())
                                val tasksLeft = tasksToCompleteJob.decrementAndGet()
                                if (tasksLeft == 0) {
                                    // Verify threads first
                                    try {
                                        assertFalse(observedIoThreads.containsAll(observedDefaultThreads))
                                    } finally {
                                        jobToComplete.complete()
                                    }
                                }
                            }

                            // Sometimes launch an IO task
                            if (Random.nextInt(0..9) == 0) {
                                launch(Dispatchers.IO) {
                                    observedIoThreads.add(Thread.currentThread())
                                    assertTrue(Thread.currentThread().isIoDispatcherThread())
                                }
                            }
                        }
                    }
                }

                withContext(Dispatchers.Default) {
                    barrier.await()

                    while (!jobToComplete.isCompleted) {
                        val result = runSingleTaskFromCurrentSystemDispatcher()
                        if (result == 0L) {
                            continue
                        } else if (result >= 0L) {
                            delay(result.toDuration(DurationUnit.NANOSECONDS))
                        } else {
                            delay(10)
                        }
                    }
                    assertTrue(Thread.currentThread() in observedDefaultThreads)
                }
                coroutineContext.job.children.toList().joinAll()
            }
        }
    }
}
