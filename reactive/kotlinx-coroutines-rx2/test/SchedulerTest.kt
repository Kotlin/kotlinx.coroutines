/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.disposables.*
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
    fun testSchedulerWithNoDelay(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableWithNoDelay(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerWithNoDelay(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableWithNoDelay(scheduler.createWorker()::schedule)
    }

    private suspend fun testRunnableWithNoDelay(block: RunnableNoDelay) {
        expect(1)
        suspendCancellableCoroutine<Unit> {
            block(Runnable {
                expect(2)
                it.resume(Unit)
            })
        }
        yield()
        finish(3)
    }

    @Test
    fun testSchedulerWithDelay(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableWithDelay(scheduler::scheduleDirect, 300)
    }

    @Test
    fun testSchedulerWorkerWithDelay(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableWithDelay(scheduler.createWorker()::schedule, 300)
    }

    @Test
    fun testSchedulerWithZeroDelay(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableWithDelay(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerWithZeroDelay(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableWithDelay(scheduler.createWorker()::schedule)
    }

    private suspend fun testRunnableWithDelay(block: RunnableWithDelay, delayMillis: Long = 0) {
        expect(1)
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        suspendCancellableCoroutine<Unit> {
            block(Runnable {
                expect(2)
                it.resume(Unit)
            }, delayMillis, TimeUnit.MILLISECONDS)
        }

        scheduler.shutdown()
        finish(3)
    }

    @Test
    fun testAsSchedulerWithNegativeDelay(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableWithDelay(scheduler::scheduleDirect, -1)
    }

    @Test
    fun testAsSchedulerWorkerWithNegativeDelay(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableWithDelay(scheduler.createWorker()::schedule, -1)
    }

    @Test
    fun testSchedulerDisposeDuringDelay(): Unit = runBlockingTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableDisposeDuringDelay(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerDisposeDuringDelay(): Unit = runBlockingTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableDisposeDuringDelay(scheduler.createWorker()::schedule)
    }

    private suspend fun testRunnableDisposeDuringDelay(block: RunnableWithDelay) {
        expect(1)
        val delayMillis = 300L
        val disposable = block(Runnable {
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
    fun testSchedulerImmediateDispose(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableImmediateDispose(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerImmediateDispose(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableImmediateDispose(scheduler.createWorker()::schedule)
    }

    private suspend fun testRunnableImmediateDispose(block: RunnableNoDelay) {
        expect(1)
        val disposable = block(Runnable {
            expectUnreached()
        })
        disposable.dispose()
        yield()
        finish(2)
    }

    @Test
    fun testSchedulerWorksWithSchedulerCoroutineDispatcher(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableWorksWithSchedulerCoroutineDispatcher(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerWorksWithSchedulerCoroutineDispatcher(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableWorksWithSchedulerCoroutineDispatcher(scheduler.createWorker()::schedule)
    }

    private suspend fun testRunnableWorksWithSchedulerCoroutineDispatcher(block: RunnableNoDelay) {
        expect(1)

        suspendCancellableCoroutine<Unit> {
            block(Runnable {
                expect(2)
                it.resume(Unit)
            })
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
    fun testSchedulerExpectRxPluginsCall(): Unit = runBlockingTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        testRunnableExpectRxPluginsCall(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerExpectRxPluginsCall(): Unit = runBlockingTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        testRunnableExpectRxPluginsCall(scheduler.createWorker()::schedule)
    }

    private suspend fun TestCoroutineScope.testRunnableExpectRxPluginsCall(block: RunnableNoDelay) {
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
                block(Runnable {
                    expect(5)
                    it.resume(Unit)
                })
                expect(3)
                resumeDispatcher()
            }
        }

        RxJavaPlugins.setScheduleHandler(null)
        scheduler.shutdown()
        finish(6)
    }

    @Test
    fun testSchedulerExpectRxPluginsCallWithDelay(): Unit = runBlockingTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        testRunnableExpectRxPluginsCallDelay(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerExpectRxPluginsCallWithDelay(): Unit = runBlockingTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        val worker = scheduler.createWorker()
        testRunnableExpectRxPluginsCallDelay(worker::schedule)
    }

    private suspend fun TestCoroutineScope.testRunnableExpectRxPluginsCallDelay(block: RunnableWithDelay) {
        expect(1)

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()

        setScheduler(2, 4)

        pauseDispatcher {
            suspendCancellableCoroutine<Unit> {
                block(Runnable {
                    expect(5)
                    RxJavaPlugins.setScheduleHandler(null)
                    it.resume(Unit)
                }, 300, TimeUnit.MILLISECONDS)
                expect(3)
                resumeDispatcher()
            }
        }

        RxJavaPlugins.setScheduleHandler(null)
        scheduler.shutdown()
        finish(6)
    }

    private fun setScheduler(expectedCountOnSchedule: Int, expectCountOnRun: Int) {
        RxJavaPlugins.setScheduleHandler(Function {
            expect(expectedCountOnSchedule)
            Runnable {
                expect(expectCountOnRun)
                it.run()
            }
        })
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

        val iterations = 2
        coroutineScope {
            for (i in (0..iterations)) {
                suspendCancellableCoroutine<Unit> {
                    worker.schedule(Runnable {
                        expect(2 + i)
                        it.resume(Unit)
                    })
                }
            }
        }
        yield()
        finish((iterations + 2) + 1)
    }

    /**
     * @see [testSchedulerWorkerSequentialOrdering]
     */
    @Test
    fun testSchedulerWorkerSequentialOrderingDelayed(): Unit = runTest {
        expect(1)

        val scheduler = Dispatchers.Default.asScheduler()

        val worker = scheduler.createWorker()

        val iterations = 2
        coroutineScope {
            for (i in (0..iterations)) {
                suspendCancellableCoroutine<Unit> {
                    worker.schedule(Runnable {
                        expect(2 + i)
                        it.resume(Unit)
                    }, 10, TimeUnit.MILLISECONDS)
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
    fun testSchedulerWorkerSequentialWithObservables(): Unit = runBlockingTest {
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

    /**
     * Test that ensures that delays are actually respected (tasks scheduled sooner in the future run before tasks scheduled later,
     * even when the later task is submitted before the earlier one)
     *
     * NOTE: not using [runBlockingTest] because of infamous "this job has not completed yet" error:
     *
     * https://github.com/Kotlin/kotlinx.coroutines/issues/1204
     */
    @Test
    fun testSchedulerRespectsDelays(): Unit = runTest {
        val scheduler = Dispatchers.Default.asScheduler()
        testRunnableRespectsDelays(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerRespectsDelays(): Unit = runTest {
        val scheduler = Dispatchers.Default.asScheduler()
        testRunnableRespectsDelays(scheduler.createWorker()::schedule)
    }

    private suspend fun testRunnableRespectsDelays(block: RunnableWithDelay) {
        expect(1)

        coroutineScope {
            launch {
                suspendCancellableCoroutine<Unit> {
                    block(Runnable {
                        println("running block for scheduler #1")
                        expect(3)
                        it.resume(Unit)
                    }, 100, TimeUnit.MILLISECONDS)
                }
            }

            launch {
                suspendCancellableCoroutine<Unit> {
                    block(Runnable {
                        println("running block for scheduler #2")
                        expect(2)
                        it.resume(Unit)
                    }, 1, TimeUnit.MILLISECONDS)
                }
            }
        }

        finish(4)
    }
}

private typealias RunnableNoDelay = (Runnable) -> Disposable
private typealias RunnableWithDelay = (Runnable, Long, TimeUnit) -> Disposable