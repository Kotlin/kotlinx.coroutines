/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class UnconfinedConcurrentTest : TestBase() {
    private val threads = 4
    private val executor = newFixedThreadPoolContext(threads, "UnconfinedConcurrentTest")
    private val threadLocal = ThreadLocal<Int>()

    @After
    fun tearDown() {
        executor.close()
    }

    @Test(timeout = 10_000L)
    fun testConcurrent() = runTest {
        val iterations = 10_000
        val startBarrier = CyclicBarrier(threads + 1)
        val finishLatch = CountDownLatch(threads)

        repeat(threads) { id ->
            launch(executor) {
                startBarrier.await()
                repeat(iterations) {
                    threadLocal.set(0)
                    launch(Dispatchers.Unconfined) {
                        assertEquals(0, threadLocal.get())
                        launch(Dispatchers.Unconfined) {
                            assertEquals(id, threadLocal.get())
                        }

                        threadLocal.set(id)
                    }
                }

                finishLatch.countDown()
            }
        }

        startBarrier.await()
        finishLatch.await()
    }
}
