/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.functions.*
import io.reactivex.observers.*
import io.reactivex.plugins.*
import io.reactivex.schedulers.*
import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
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
    fun testIoScheduler(): Unit = runTest {
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
    fun testAsSchedulerWithNoDelay(): Unit = runTest {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        suspendCancellableCoroutine<Unit> {
            scheduler.scheduleDirect {
                val t1 = Thread.currentThread()
                assertSame(t1, mainThread)
                expect(2)
                it.resume(Unit)
            }
        }
        yield()
        finish(3)
    }

    @Test
    fun testAsSchedulerWithDelay(): Unit = runTest {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        val delayMillis = 300L
        suspendCancellableCoroutine<Unit> {
            scheduler.scheduleDirect({
                val t1 = Thread.currentThread()
                assertSame(t1, mainThread)
                expect(2)
                it.resume(Unit)
            }, delayMillis, TimeUnit.MILLISECONDS)
        }
        finish(3)
    }

    @Test
    fun testAsSchedulerWithZeroDelay(): Unit = runTest {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        suspendCancellableCoroutine<Unit> {
            scheduler.scheduleDirect({
                val t1 = Thread.currentThread()
                assertSame(t1, mainThread)
                expect(2)
                it.resume(Unit)
            }, 0, TimeUnit.MILLISECONDS)
        }

        scheduler.shutdown()
        finish(3)
    }

    @Test
    fun testAsSchedulerWithNegativeDelay(): Unit = runTest {
        expect(1)
        val mainThread = Thread.currentThread()
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        suspendCancellableCoroutine<Unit> {
            scheduler.scheduleDirect({
                val t1 = Thread.currentThread()
                assertSame(t1, mainThread)
                expect(2)
                it.resume(Unit)
            }, -1, TimeUnit.MILLISECONDS)
        }
        yield()
        finish(3)
    }

    @Test
    fun testDisposeDuringDelay(): Unit = runTest {
        expect(1)
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        val delayMillis = 300L
        val disposable = scheduler.scheduleDirect({
            expectUnreached()
        }, delayMillis, TimeUnit.MILLISECONDS)
        delay(100)
        expect(2)
        disposable.dispose()
        delay(300)
        yield()
        finish(3)
    }

    @Test
    fun testImmediateDispose(): Unit = runTest {
        expect(1)
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        val disposable = scheduler.scheduleDirect {
            expectUnreached()
        }
        disposable.dispose()
        yield()
        finish(2)
    }

    @Test
    fun testAsSchedulerWorksWithSchedulerCoroutineDispatcher(): Unit = runTest {
        expect(1)

        val dispatcher = Schedulers.io().asCoroutineDispatcher()
        val scheduler = dispatcher.asScheduler()
        suspendCancellableCoroutine<Unit> {
            scheduler.scheduleDirect {
                expect(2)
                it.resume(Unit)
            }
        }
        finish(3)
    }

    @Test
    fun tesConvertDispatcherToOriginalScheduler(): Unit = runTest {
        expect(1)

        val originalScheduler = Schedulers.io()
        val dispatcher = originalScheduler.asCoroutineDispatcher()
        val scheduler = dispatcher.asScheduler()
        assertEquals(originalScheduler, scheduler)

        finish(2)
    }

    @Test
    fun tesConvertSchedulerToOriginalDispatcher(): Unit = runTest {
        expect(1)

        val originalDispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = originalDispatcher.asScheduler()
        val dispatcher = scheduler.asCoroutineDispatcher()
        assertEquals(originalDispatcher, dispatcher)

        finish(2)
    }

    @Test
    fun testExpectRxPluginsCall(): Unit = runBlockingTest {
        expect(1)

        fun setScheduler(expectedCountOnSchedule: Int, expectCountOnRun: Int) {
            RxJavaPlugins.setScheduleHandler(Function {
                expect(expectedCountOnSchedule)
                Runnable {
                    expect(expectCountOnRun)
                    it.run()
                }
            })
        }

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()

        setScheduler(2, 4)

        pauseDispatcher {
            suspendCancellableCoroutine<Unit> {
                scheduler.scheduleDirect {
                    expect(5)
                    it.resume(Unit)
                }
                expect(3)
                resumeDispatcher()
            }
        }

        setScheduler(6, 8)
        pauseDispatcher {
            suspendCancellableCoroutine<Unit> {
                scheduler.scheduleDirect({
                    expect(9)
                    RxJavaPlugins.setScheduleHandler(null)
                    it.resume(Unit)
                }, 300, TimeUnit.MILLISECONDS)
                expect(7)
                resumeDispatcher()
            }
        }

        scheduler.shutdown()
        finish(10)
    }

    /**
     * Let's test the [Scheduler.Worker] to make sure it satisfies the documented constraint of running all work
     * sequentially
     */
    @Test
    fun testSchedulerWorkerSequentialOrdering(): Unit = runTest {
        expect(1)

        val scheduler = Dispatchers.Default.asScheduler()

        val worker = scheduler.createWorker()

        val iterations = 5
        coroutineScope {
            for (i in (0..iterations)) {
                launch {
                    suspendCancellableCoroutine<Unit> {
                        worker.schedule(Runnable {
                            runBlocking {
                                if (i % 2 == 0) {
                                    // add delays to ensure sequential nature
                                    delay(100)
                                }
                                expect(2 + i)
                                it.resume(Unit)
                            }
                        })
                    }
                    yield()
                }
            }
        }
        yield()
        finish((iterations + 2) + 1)
    }

    /**
     * Let's test the [Scheduler.Worker] to make sure it satisfies the documented constraint of running all work
     * sequentially using RxJava primitives
     */
    @Test
    fun testSchedulerWorkerSequentialWithObservables(): Unit = runTest {
        expect(1)

        val scheduler = Dispatchers.Default.asScheduler()

        val testObservable = Observable
            .create<Int> {
                it.onNext(1)
                it.onNext(2)
                it.onComplete()
            }
            .observeOn(scheduler)
            .map {
                runBlocking {
                    if (it == 1) {
                        // delay by some time. we expect that even with delay this iteration should be first
                        delay(100)
                    }
                    it + 1
                }
            }
            .subscribeOn(scheduler)

        val testObserver = TestObserver<Int>()
        testObservable.subscribe(testObserver)
        testObservable.blockingSubscribe()
        testObserver.apply {
            assertValueCount(2)
            assertResult(2, 3)
            dispose()
        }
        finish(2)
    }
}