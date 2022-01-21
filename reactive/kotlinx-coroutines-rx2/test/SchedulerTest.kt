/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.disposables.*
import io.reactivex.observers.*
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

    private fun runSchedulerTest(nThreads: Int = 1, action: (Scheduler) -> Unit) {
        val future = CompletableFuture<Unit>()
        try {
            newFixedThreadPoolContext(nThreads, "test").use { dispatcher ->
                RxJavaPlugins.setErrorHandler {
                    if (!future.completeExceptionally(it)) {
                        handleUndeliverableException(it, dispatcher)
                    }
                }
                action(dispatcher.asScheduler())
            }
        } finally {
            RxJavaPlugins.setErrorHandler(null)
        }
        future.complete(Unit)
        future.getNow(Unit) // rethrow any encountered errors
    }

    /**
     * Tests [Scheduler.scheduleDirect] for [CoroutineDispatcher.asScheduler] on a single-threaded dispatcher.
     */
    @Test
    fun testSingleThreadedDispatcherDirect(): Unit = runSchedulerTest {
        val mainThread = Thread.currentThread()
        val cdl1 = CountDownLatch(1)
        val cdl2 = CountDownLatch(1)
        expect(1)
        it.scheduleDirect({
            assertNotSame(mainThread, Thread.currentThread())
            cdl2.countDown()
        }, 300, TimeUnit.MILLISECONDS)
        it.scheduleDirect {
            expect(2)
            assertNotSame(mainThread, Thread.currentThread())
            cdl1.countDown()
        }
        cdl1.await()
        cdl2.await()
        finish(3)
    }

    /**
     * Test cancelling [Scheduler.scheduleDirect] for [CoroutineDispatcher.asScheduler].
     */
    @Test
    fun testCancellingDirect(): Unit = runSchedulerTest {
        // cancel the task before it has a chance to run.
        val handle1 = it.scheduleDirect({
            throw IllegalStateException("should have been successfully cancelled")
        }, 10_000, TimeUnit.MILLISECONDS)
        handle1.dispose()
        // cancel the task after it started running.
        val cdl1 = CountDownLatch(1)
        val cdl2 = CountDownLatch(1)
        val handle2 = it.scheduleDirect({
            cdl1.countDown()
            cdl2.await()
            if (Thread.interrupted())
                throw IllegalStateException("cancelling the task should not interrupt the thread")
        }, 100, TimeUnit.MILLISECONDS)
        cdl1.await()
        handle2.dispose()
        cdl2.countDown()
    }

    /**
     * Test shutting down [CoroutineDispatcher.asScheduler].
     */
    @Test
    fun testShuttingDown() {
        val n = 5
        runSchedulerTest(nThreads = n) { scheduler ->
            val cdl1 = CountDownLatch(n)
            val cdl2 = CountDownLatch(1)
            val cdl3 = CountDownLatch(n)
            repeat(n) {
                scheduler.scheduleDirect {
                    cdl1.countDown()
                    try {
                        cdl2.await()
                    } catch (e: InterruptedException) {
                        // this is the expected outcome
                        cdl3.countDown()
                    }
                }
            }
            cdl1.await()
            scheduler.shutdown()
            if (!cdl3.await(1, TimeUnit.SECONDS)) {
                cdl2.countDown()
                error("the tasks were not cancelled when the scheduler was shut down")
            }
        }
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

    private suspend fun testRunnableWithNoDelay(block: RxSchedulerBlockNoDelay) {
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

    private suspend fun testRunnableWithDelay(block: RxSchedulerBlockWithDelay, delayMillis: Long = 0) {
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
    fun testSchedulerDisposeDuringDelay(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableDisposeDuringDelay(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerDisposeDuringDelay(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableDisposeDuringDelay(scheduler.createWorker()::schedule)
    }

    private suspend fun testRunnableDisposeDuringDelay(block: RxSchedulerBlockWithDelay) {
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

    private suspend fun testRunnableImmediateDispose(block: RxSchedulerBlockNoDelay) {
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
        expect(1)
        suspendCancellableCoroutine<Unit> {
            scheduler.scheduleDirect {
                expect(2)
                it.resume(Unit)
            }
        }
        finish(3)
    }

    @Test
    fun testConvertDispatcherToOriginalScheduler(): Unit = runTest {
        expect(1)

        val originalScheduler = Schedulers.io()
        val dispatcher = originalScheduler.asCoroutineDispatcher()
        val scheduler = dispatcher.asScheduler()
        assertEquals(originalScheduler, scheduler)

        finish(2)
    }

    @Test
    fun testConvertSchedulerToOriginalDispatcher(): Unit = runTest {
        expect(1)

        val originalDispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = originalDispatcher.asScheduler()
        val dispatcher = scheduler.asCoroutineDispatcher()
        assertEquals(originalDispatcher, dispatcher)

        finish(2)
    }

    @Test
    fun testSchedulerExpectRxPluginsCall(): Unit = runTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        testRunnableExpectRxPluginsCall(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerExpectRxPluginsCall(): Unit = runTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        testRunnableExpectRxPluginsCall(scheduler.createWorker()::schedule)
    }

    private suspend fun testRunnableExpectRxPluginsCall(block: RxSchedulerBlockNoDelay) {
        expect(1)

        fun setScheduler(expectedCountOnSchedule: Int, expectCountOnRun: Int) {
            RxJavaPlugins.setScheduleHandler {
                expect(expectedCountOnSchedule)
                Runnable {
                    expect(expectCountOnRun)
                    it.run()
                }
            }
        }

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()

        setScheduler(2, 4)

        suspendCancellableCoroutine<Unit> {
            block(Runnable {
                expect(5)
                it.resume(Unit)
            })
            expect(3)
        }

        RxJavaPlugins.setScheduleHandler(null)
        scheduler.shutdown()
        finish(6)
    }

    @Test
    fun testSchedulerExpectRxPluginsCallWithDelay(): Unit = runTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        testRunnableExpectRxPluginsCallDelay(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerExpectRxPluginsCallWithDelay(): Unit = runTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        val worker = scheduler.createWorker()
        testRunnableExpectRxPluginsCallDelay(worker::schedule)
    }

    private suspend fun testRunnableExpectRxPluginsCallDelay(block: RxSchedulerBlockWithDelay) {
        expect(1)

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()

        setScheduler(2, 4)

        suspendCancellableCoroutine<Unit> {
            block(Runnable {
                expect(5)
                RxJavaPlugins.setScheduleHandler(null)
                it.resume(Unit)
            }, 300, TimeUnit.MILLISECONDS)
            expect(3)
        }

        RxJavaPlugins.setScheduleHandler(null)
        scheduler.shutdown()
        finish(6)
    }

    private fun setScheduler(expectedCountOnSchedule: Int, expectCountOnRun: Int) {
        RxJavaPlugins.setScheduleHandler {
            expect(expectedCountOnSchedule)
            Runnable {
                expect(expectCountOnRun)
                it.run()
            }
        }
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
                launch {
                    suspendCancellableCoroutine<Unit> {
                        worker.schedule {
                            expect(2 + i)
                            it.resume(Unit)
                        }
                    }
                    yield()
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
                    worker.schedule({
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

    /**
     * Test that ensures that delays are actually respected (tasks scheduled sooner in the future run before tasks scheduled later,
     * even when the later task is submitted before the earlier one)
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

    private suspend fun testRunnableRespectsDelays(block: RxSchedulerBlockWithDelay) {
        expect(1)

        coroutineScope {
            launch {
                suspendCancellableCoroutine<Unit> {
                    block(Runnable {
                        expect(3)
                        it.resume(Unit)
                    }, 100, TimeUnit.MILLISECONDS)
                }
            }

            launch {
                suspendCancellableCoroutine<Unit> {
                    block(Runnable {
                        expect(2)
                        it.resume(Unit)
                    }, 1, TimeUnit.MILLISECONDS)
                }
            }
        }

        finish(4)
    }

    /**
     * Tests that cancelling a runnable in one worker doesn't affect work in another scheduler.
     *
     * This is part of expected behavior documented.
     */
    @Test
    fun testMultipleWorkerCancellation(): Unit = runTest {
        expect(1)

        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()

        coroutineScope {
            suspendCancellableCoroutine<Unit> {
                val workerOne = scheduler.createWorker()
                workerOne.schedule({
                    expect(3)
                    it.resume(Unit)
                }, 10, TimeUnit.MILLISECONDS)

                expect(2)

                val workerTwo = scheduler.createWorker()
                workerTwo.schedule({
                    expectUnreached()
                }, 10, TimeUnit.MILLISECONDS)
                workerTwo.dispose()
            }
        }

        finish(4)
    }
}

typealias RxSchedulerBlockNoDelay = (Runnable) -> Disposable
typealias RxSchedulerBlockWithDelay = (Runnable, Long, TimeUnit) -> Disposable