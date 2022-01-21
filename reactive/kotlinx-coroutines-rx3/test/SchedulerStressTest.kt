/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import org.junit.*
import java.util.concurrent.*

class SchedulerStressTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxCachedThreadScheduler-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    /**
     * Test that we don't get an OOM if we schedule many jobs at once. It's expected that if you don't dispose that you'd
     * see a OOM error.
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
        testRunnableDisposed(scheduler.createWorker()::schedule)
    }

    private suspend fun testRunnableDisposed(block: RxSchedulerBlockNoDelay) {
        expect(1)

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()

        val n = 2000 * stressTestMultiplier
        coroutineScope {
            repeat(n) { i ->
                launch {
                    val a = ByteArray(1000000) //1MB
                    val disposable = block(Runnable {
                        expectUnreached()
                        runBlocking {
                            keepMe(a)
                        }
                    })
                    disposable.dispose()
                    expect(i + 2)
                }
                yield()
            }
        }

        scheduler.shutdown()
        finish(n + 2)
    }

    /**
     * Test function that holds a reference. Used for testing OOM situations
     */
    private suspend fun keepMe(a: ByteArray) {
        delay(10)
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
        testRunnableDisposedDuringDelay(scheduler.createWorker()::schedule)
    }

    private suspend fun testRunnableDisposedDuringDelay(block: RxSchedulerBlockWithDelay) {
        expect(1)

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()

        val n = 2000 * stressTestMultiplier
        coroutineScope {
            repeat(n) { i ->
                val a = ByteArray(1000000) //1MB
                val delayMillis: Long = 10
                val disposable = block(Runnable {
                    runBlocking {
                        keepMe(a)
                    }
                }, delayMillis, TimeUnit.MILLISECONDS)
                disposable.dispose()
                yield()
            }
        }

        scheduler.shutdown()
        finish(2)
    }
}