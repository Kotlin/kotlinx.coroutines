/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.schedulers.Schedulers
import kotlinx.coroutines.*
import org.junit.Before
import org.junit.Test
import java.util.concurrent.TimeUnit
import kotlin.test.assertNotSame
import kotlin.test.assertSame

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
    fun `test asScheduler() with no delay`(): Unit = runBlocking {
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
    fun `test asScheduler() with delay runs block after some time`(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        val delayMillis = 300L
        scheduler.scheduleDirect({
            val t1 = Thread.currentThread()
            assertSame(t1, mainThread)
            expect(2)
        }, delayMillis, TimeUnit.MILLISECONDS)
        delay(delayMillis + 50)
        yield()
        finish(3)
    }

    @Test
    fun `test asScheduler() with delay does not run block if delay time hasn't elapsed`(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        val delayMillis = 300L
        scheduler.scheduleDirect({
            val t1 = Thread.currentThread()
            assertSame(t1, mainThread)
        }, delayMillis, TimeUnit.MILLISECONDS)
        yield()
        finish(2)
        scheduler.shutdown()
    }

    @Test
    fun `test asScheduler() properly disposes work during delay`(): Unit = runBlocking {
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
    fun `test asScheduler() properly disposes work after shutdown`(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        val delayMillis = 300L

        fun scheduleWork() =
                scheduler.scheduleDirect({
                    expectUnreached()
                    val t1 = Thread.currentThread()
                    assertSame(t1, mainThread)
                }, delayMillis, TimeUnit.MILLISECONDS)

        scheduleWork()
        scheduleWork()

        delay(100)
        expect(2)
        scheduler.shutdown()
        delay(300)
        yield()
        finish(3)
    }
}