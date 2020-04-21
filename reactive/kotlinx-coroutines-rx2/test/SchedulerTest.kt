/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.functions.*
import io.reactivex.plugins.*
import io.reactivex.schedulers.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import java.lang.Runnable
import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

class SchedulerTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxCachedThreadScheduler-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    @Test
    fun testIoScheduler(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        withContext(Schedulers.io().asCoroutineDispatcher()) {
            val t1 = Thread.currentThread()
            assertNotSame(t1, mainThread)
            expect(2)
            delay(100)
            val t2 = Thread.currentThread()
            assertNotSame(t2, mainThread)
            expect(3)
        }
        finish(4)
    }

    @Test
    fun testAsSchedulerWithNoDelay(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        scheduler.scheduleDirect {
            val t1 = Thread.currentThread()
            assertSame(t1, mainThread)
            expect(2)
        }
        yield()
        finish(3)
    }

    @Test
    fun testAsSchedulerWithDelay(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        val delayMillis = 300L
        suspendCancellableCoroutine<Unit> {
            scheduler.scheduleDirect({
                val t1 = Thread.currentThread()
                assertSame(t1, mainThread)
                finish(2)
                it.resume(Unit)
            }, delayMillis, TimeUnit.MILLISECONDS)
        }
    }

    @Test
    fun testAsSchedulerWithZeroDelay(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        scheduler.scheduleDirect({
            val t1 = Thread.currentThread()
            assertSame(t1, mainThread)
            finish(2)
        }, 0, TimeUnit.MILLISECONDS)
        yield()
    }

    @Test
    fun testAsSchedulerWithNegativeDelay(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        scheduler.scheduleDirect({
            val t1 = Thread.currentThread()
            assertSame(t1, mainThread)
            finish(2)
        }, -1, TimeUnit.MILLISECONDS)
        yield()
    }

    @Test
    fun testBlockUnreachedIfDelayed(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        val delayMillis = 300L
        val disposable = scheduler.scheduleDirect({
            expectUnreached()
            val t1 = Thread.currentThread()
            assertSame(t1, mainThread)
        }, delayMillis, TimeUnit.MILLISECONDS)
        yield()
        finish(2)
        disposable.dispose() // cleanup
    }

    @Test
    fun testDisposeDuringDelay(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        val delayMillis = 300L
        val disposable = scheduler.scheduleDirect({
            expectUnreached()
            val t1 = Thread.currentThread()
            assertSame(t1, mainThread)
        }, delayMillis, TimeUnit.MILLISECONDS)
        delay(100)
        expect(2)
        disposable.dispose()
        delay(300)
        yield()
        finish(3)
    }

    @Test
    fun testAsSchedulerWorksWithSchedulerCoroutineDispatcher(): Unit = runBlocking {
        expect(1)

        val dispatcher = Schedulers.io().asCoroutineDispatcher()
        val scheduler = dispatcher.asScheduler()
        suspendCancellableCoroutine<Unit> {
            scheduler.scheduleDirect {
                finish(3)
                it.resume(Unit)
            }
            expect(2)
        }
        ensureFinished()
    }

    @Test
    fun testAsSchedulerWithAMillionTasks(): Unit = runBlocking {
        var counter = 1
        expect(counter)

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        val numberOfJobs = 1000000
        for (i in 0..numberOfJobs) {
            scheduler.scheduleDirect {
                expect(++counter)
            }
        }
        yield()
        finish(1000003)
    }

    @Test
    fun testAsSchedulerWithAMillionTasksWithDelay(): Unit = runBlocking {
        expect(1)

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        val numberOfJobs = 1000000
        for (i in 0..numberOfJobs) {
            val disposable = scheduler.scheduleDirect({
                expectUnreached()
            }, 100, TimeUnit.MILLISECONDS)
            disposable.dispose()
        }
        yield()
        finish(2)
    }

    @Test
    fun testExpectRxPluginsCall(): Unit = runBlocking {
        var expectCounter = 0
        expect(++expectCounter)

        fun setScheduler(expectCountOnRun: Int) {
            RxJavaPlugins.setScheduleHandler(Function {
                Runnable {
                    expect(expectCountOnRun)
                    it.run()
                }
            })
        }

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()

        setScheduler(2)
        scheduler.scheduleDirect {
            expect(3)
        }

        setScheduler(4)
        suspendCancellableCoroutine<Unit> {
            scheduler.scheduleDirect({
                finish(5)
                RxJavaPlugins.setScheduleHandler(null)
                it.resume(Unit)
            }, 300, TimeUnit.MILLISECONDS)
        }
    }
}