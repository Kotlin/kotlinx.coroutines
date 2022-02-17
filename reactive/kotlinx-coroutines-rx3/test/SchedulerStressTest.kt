/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import kotlinx.coroutines.*
import org.junit.*
import java.util.concurrent.*

class SchedulerStressTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxCachedThreadScheduler-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    /**
     * Test that we don't get an OOM if we schedule many jobs at once.
     * It's expected that if you don't dispose you'd see an OOM error.
     */
    @Test
    fun testSchedulerDisposed(): Unit = runTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        testRunnableDisposed(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerDisposed(): Unit = runTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        val worker = scheduler.createWorker()
        testRunnableDisposed(worker::schedule)
    }

    private suspend fun testRunnableDisposed(block: RxSchedulerBlockNoDelay) {
        val n = 2000 * stressTestMultiplier
        repeat(n) {
            val a = ByteArray(1000000) //1MB
            val disposable = block(Runnable {
                keepMe(a)
                expectUnreached()
            })
            disposable.dispose()
            yield() // allow the scheduled task to observe that it was disposed
        }
    }

    /**
     * Test function that holds a reference. Used for testing OOM situations
     */
    private fun keepMe(a: ByteArray) {
        Thread.sleep(a.size / (a.size + 1) + 10L)
    }

    /**
     * Test that we don't get an OOM if we schedule many delayed jobs at once. It's expected that if you don't dispose that you'd
     * see a OOM error.
     */
    @Test
    fun testSchedulerDisposedDuringDelay(): Unit = runTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        testRunnableDisposedDuringDelay(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerDisposedDuringDelay(): Unit = runTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        val worker = scheduler.createWorker()
        testRunnableDisposedDuringDelay(worker::schedule)
    }

    private fun testRunnableDisposedDuringDelay(block: RxSchedulerBlockWithDelay) {
        val n = 2000 * stressTestMultiplier
        repeat(n) {
            val a = ByteArray(1000000) //1MB
            val delayMillis: Long = 10
            val disposable = block(Runnable {
                keepMe(a)
                expectUnreached()
            }, delayMillis, TimeUnit.MILLISECONDS)
            disposable.dispose()
        }
    }
}
