/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import java.util.concurrent.*
import java.util.concurrent.CancellationException
import kotlin.test.*

class ThreadSafeHeapStressTest : TestBase() {
    private class DisposableNode : EventLoopImplBase.DelayedTask(1L) {
        override fun run() {
        }
    }

    @Test
    fun testConcurrentRemoveDispose() = runTest {
        val heap = EventLoopImplBase.DelayedTaskQueue(1)
        repeat(10_000 * stressTestMultiplierSqrt) {
            withContext(Dispatchers.Default) {
                val node = DisposableNode()
                val barrier = CyclicBarrier(2)
                launch {
                    heap.addLast(node)
                    barrier.await()
                    heap.remove(node)
                }
                launch {
                    barrier.await()
                    Thread.yield()
                    node.dispose()
                }
            }
        }
    }

    @Test()
    fun testConcurrentAddDispose() = runTest {
        repeat(10_000 * stressTestMultiplierSqrt) {
            val jobToCancel = Job()
            val barrier = CyclicBarrier(2)
            val jobToJoin = launch(Dispatchers.Default) {
                barrier.await()
                jobToCancel.cancelAndJoin()
            }

            try {
                runBlocking { // Use event loop impl
                    withContext(jobToCancel) {
                        // This one is to work around heap allocation optimization
                        launch(start = CoroutineStart.UNDISPATCHED) {
                            delay(100_000)
                        }
                        barrier.await()
                        delay(100_000)
                    }
                }
            } catch (e: CancellationException) {
                // Expected exception
            }
            jobToJoin.join()
        }
    }
}
