/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import kotlinx.coroutines.*
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
    fun testScheduleDirectDisposed(): Unit = runTest {
        expect(1)

        suspend fun keepMe(a: ByteArray) {
            delay(10)
        }

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()

        val n = 2000 * stressTestMultiplier
        coroutineScope {
            repeat(n) { i ->
                val a = ByteArray(1000000) //1MB
                val disposable = scheduler.scheduleDirect {
                    runBlocking {
                        keepMe(a)
                    }
                }
                disposable.dispose()
                expect(i + 2)
                yield()
            }
        }

        scheduler.shutdown()
        finish(n + 2)
    }

    /**
     * Test that we don't get an OOM if we schedule many delayed jobs at once. It's expected that if you don't dispose that you'd
     * see a OOM error.
     */
    @Test
    fun testScheduleDirectDisposedDuringDelay(): Unit = runTest {
        expect(1)

        suspend fun keepMe(a: ByteArray) {
            delay(10)
        }

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()

        val n = 2000 * stressTestMultiplier
        coroutineScope {
            repeat(n) { i ->
                val a = ByteArray(1000000) //1MB
                val disposable = scheduler.scheduleDirect({
                    runBlocking {
                        keepMe(a)
                    }
                }, 10, TimeUnit.MILLISECONDS)
                disposable.dispose()
                expect(i + 2)
                yield()
            }
        }

        scheduler.shutdown()
        finish(n + 2)
    }
}