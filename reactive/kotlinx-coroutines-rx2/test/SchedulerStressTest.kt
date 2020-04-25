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

    @Ignore
    @Test
    fun testScheduleDirectDisposed(): Unit = runTest {
        expect(1)

        fun keepMe(a: ByteArray) {
            // does nothing, makes sure the variable is kept in state-machine
        }

        val d = async {
            delay(Long.MAX_VALUE)
        }

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()

        val n = 100
        coroutineScope {
            repeat(n) {
                launch {
                    val disposable = scheduler.scheduleDirect {
                        val a = ByteArray(1000000) //1MB
                        runBlocking {
                            d.await()
                            keepMe(a)
                        }
                    }
                    disposable.dispose()
                    check(disposable.isDisposed)
                }
                yield()
            }
        }

        scheduler.shutdown()
        finish(2)
    }

    @Ignore
    @Test
    fun testScheduleDirectDisposedDuringDelay(): Unit = runTest {
        expect(1)

        fun keepMe(a: ByteArray) {
            // does nothing, makes sure the variable is kept in state-machine
        }

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()

        val n = 2000 * stressTestMultiplier
        coroutineScope {
            repeat(n) {
                launch {
                    val a = ByteArray(1000000) //1MB
                    val disposable = scheduler.scheduleDirect({
                        expectUnreached()
                    }, 50, TimeUnit.MILLISECONDS)
                    disposable.dispose()
                    check(disposable.isDisposed)
                    delay(60)
                    keepMe(a)
                }
            }
        }

        finish(2)
    }
}