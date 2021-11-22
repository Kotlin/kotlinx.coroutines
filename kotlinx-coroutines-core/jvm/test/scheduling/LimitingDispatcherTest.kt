/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.coroutines.*
import org.junit.*
import java.util.concurrent.*

class LimitingDispatcherTest : SchedulerTestBase() {

    @Test(expected = IllegalArgumentException::class)
    fun testNegativeView() {
        view(-1)
    }

    @Test(expected = IllegalArgumentException::class)
    fun testZeroView() {
        view(0)
    }

    @Test(timeout = 10_000)
    fun testBlockingInterleave() = runBlocking {
        corePoolSize = 3
        val view = view(2)
        val blocking = blockingDispatcher(4)
        val barrier = CyclicBarrier(6)
        val tasks = ArrayList<Job>(6)
        repeat(2) {
            tasks += async(view) {
                barrier.await()
            }

            repeat(2) {
                tasks += async(blocking) {
                    barrier.await()
                }
            }
        }

        tasks.joinAll()
    }
}
