/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.disposables.*
import io.reactivex.plugins.*
import io.reactivex.schedulers.*
import kotlinx.coroutines.*
import kotlinx.coroutines.sync.*
import org.junit.*
import org.junit.Test
import java.lang.Runnable
import java.util.concurrent.*
import java.util.concurrent.atomic.AtomicReference
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

    /** Tests [toString] implementations of [CoroutineDispatcher.asScheduler] and its [Scheduler.Worker]. */
    @Test
    fun testSchedulerToString() {
        val name = "Dispatchers.Default"
        val scheduler = Dispatchers.Default.asScheduler()
        assertContains(scheduler.toString(), name)
        val worker = scheduler.createWorker()
        val activeWorkerName = worker.toString()
        assertContains(worker.toString(), name)
        worker.dispose()
        val disposedWorkerName = worker.toString()
        assertNotEquals(activeWorkerName, disposedWorkerName)
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

    private fun ensureSeparateThread(schedule: (Runnable, Long, TimeUnit) -> Unit, scheduleNoDelay: (Runnable) -> Unit) {
        val mainThread = Thread.currentThread()
        val cdl1 = CountDownLatch(1)
        val cdl2 = CountDownLatch(1)
        expect(1)
        val thread = AtomicReference<Thread?>(null)
        fun checkThread() {
            val current = Thread.currentThread()
            thread.getAndSet(current)?.let { assertEquals(it, current) }
        }
        schedule({
            assertNotSame(mainThread, Thread.currentThread())
            checkThread()
            cdl2.countDown()
        }, 300, TimeUnit.MILLISECONDS)
        scheduleNoDelay {
            expect(2)
            checkThread()
            assertNotSame(mainThread, Thread.currentThread())
            cdl1.countDown()
        }
        cdl1.await()
        cdl2.await()
        finish(3)
    }

    /**
     * Tests [Scheduler.scheduleDirect] for [CoroutineDispatcher.asScheduler] on a single-threaded dispatcher.
     */
    @Test
    fun testSingleThreadedDispatcherDirect(): Unit = runSchedulerTest(1) {
        ensureSeparateThread(it::scheduleDirect, it::scheduleDirect)
    }

    /**
     * Tests [Scheduler.Worker.schedule] for [CoroutineDispatcher.asScheduler] running its tasks on the correct thread.
     */
    @Test
    fun testSingleThreadedWorker(): Unit = runSchedulerTest(1) {
        val worker = it.createWorker()
        ensureSeparateThread(worker::schedule, worker::schedule)
    }

    private fun checkCancelling(schedule: (Runnable, Long, TimeUnit) -> Disposable) {
        // cancel the task before it has a chance to run.
        val handle1 = schedule({
            throw IllegalStateException("should have been successfully cancelled")
        }, 10_000, TimeUnit.MILLISECONDS)
        handle1.dispose()
        // cancel the task after it started running.
        val cdl1 = CountDownLatch(1)
        val cdl2 = CountDownLatch(1)
        val handle2 = schedule({
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
     * Test cancelling [Scheduler.scheduleDirect] for [CoroutineDispatcher.asScheduler].
     */
    @Test
    fun testCancellingDirect(): Unit = runSchedulerTest {
        checkCancelling(it::scheduleDirect)
    }

    /**
     * Test cancelling [Scheduler.Worker.schedule] for [CoroutineDispatcher.asScheduler].
     */
    @Test
    fun testCancellingWorker(): Unit = runSchedulerTest {
        val worker = it.createWorker()
        checkCancelling(worker::schedule)
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

    /** Tests that there are no uncaught exceptions if [Disposable.dispose] on a worker happens when tasks are present. */
    @Test
    fun testDisposingWorker() = runTest {
        val dispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = dispatcher.asScheduler()
        val worker = scheduler.createWorker()
        yield() // so that the worker starts waiting on the channel
        assertFalse(worker.isDisposed)
        worker.dispose()
        assertTrue(worker.isDisposed)
    }

    /** Tests trying to use a [Scheduler.Worker]/[Scheduler] after [Scheduler.Worker.dispose]/[Scheduler.shutdown]. */
    @Test
    fun testSchedulingAfterDisposing() = runSchedulerTest {
        expect(1)
        val worker = it.createWorker()
        // use CDL to ensure that the worker has properly initialized
        val cdl1 = CountDownLatch(1)
        setScheduler(2, 3)
        val disposable1 = worker.schedule {
            cdl1.countDown()
        }
        cdl1.await()
        expect(4)
        assertFalse(disposable1.isDisposed)
        setScheduler(6, -1)
        // check that the worker automatically disposes of the tasks after being disposed
        assertFalse(worker.isDisposed)
        worker.dispose()
        assertTrue(worker.isDisposed)
        expect(5)
        val disposable2 = worker.schedule {
            expectUnreached()
        }
        assertTrue(disposable2.isDisposed)
        setScheduler(7, 8)
        // ensure that the scheduler still works
        val cdl2 = CountDownLatch(1)
        val disposable3 = it.scheduleDirect {
            cdl2.countDown()
        }
        cdl2.await()
        expect(9)
        assertFalse(disposable3.isDisposed)
        // check that the scheduler automatically disposes of the tasks after being shut down
        it.shutdown()
        setScheduler(10, -1)
        val disposable4 = it.scheduleDirect {
            expectUnreached()
        }
        assertTrue(disposable4.isDisposed)
        RxJavaPlugins.setScheduleHandler(null)
        finish(11)
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
        suspendCancellableCoroutine<Unit> {
            block({
                expect(2)
                it.resume(Unit)
            }, delayMillis, TimeUnit.MILLISECONDS)
        }
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
    fun testSchedulerImmediateDispose(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableImmediateDispose(scheduler::scheduleDirect)
    }

    @Test
    fun testSchedulerWorkerImmediateDispose(): Unit = runTest {
        val scheduler = (currentDispatcher() as CoroutineDispatcher).asScheduler()
        testRunnableImmediateDispose(scheduler.createWorker()::schedule)
    }

    private fun testRunnableImmediateDispose(block: RxSchedulerBlockNoDelay) {
        val disposable = block {
            expectUnreached()
        }
        disposable.dispose()
    }

    @Test
    fun testConvertDispatcherToOriginalScheduler(): Unit = runTest {
        val originalScheduler = Schedulers.io()
        val dispatcher = originalScheduler.asCoroutineDispatcher()
        val scheduler = dispatcher.asScheduler()
        assertSame(originalScheduler, scheduler)
    }

    @Test
    fun testConvertSchedulerToOriginalDispatcher(): Unit = runTest {
        val originalDispatcher = currentDispatcher() as CoroutineDispatcher
        val scheduler = originalDispatcher.asScheduler()
        val dispatcher = scheduler.asCoroutineDispatcher()
        assertSame(originalDispatcher, dispatcher)
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
        setScheduler(2, 4)
        suspendCancellableCoroutine<Unit> {
            block(Runnable {
                expect(5)
                it.resume(Unit)
            })
            expect(3)
        }
        RxJavaPlugins.setScheduleHandler(null)
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
        setScheduler(2, 4)
        suspendCancellableCoroutine<Unit> {
            block({
                expect(5)
                it.resume(Unit)
            }, 10, TimeUnit.MILLISECONDS)
            expect(3)
        }
        RxJavaPlugins.setScheduleHandler(null)
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
     * Tests that [Scheduler.Worker] runs all work sequentially.
     */
    @Test
    fun testWorkerSequentialOrdering() = runTest {
        expect(1)
        val scheduler = Dispatchers.Default.asScheduler()
        val worker = scheduler.createWorker()
        val iterations = 100
        for (i in 0..iterations) {
            worker.schedule {
                expect(2 + i)
            }
        }
        suspendCoroutine<Unit> {
            worker.schedule {
                it.resume(Unit)
            }
        }
        finish((iterations + 2) + 1)
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
        val semaphore = Semaphore(2, 2)
        block({
            expect(3)
            semaphore.release()
        }, 100, TimeUnit.MILLISECONDS)
        block({
            expect(2)
            semaphore.release()
        }, 1, TimeUnit.MILLISECONDS)
        semaphore.acquire()
        semaphore.acquire()
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
        suspendCancellableCoroutine<Unit> {
            val workerOne = scheduler.createWorker()
            workerOne.schedule({
                expect(3)
                it.resume(Unit)
            }, 50, TimeUnit.MILLISECONDS)
            val workerTwo = scheduler.createWorker()
            workerTwo.schedule({
                expectUnreached()
            }, 1000, TimeUnit.MILLISECONDS)
            workerTwo.dispose()
            expect(2)
        }
        finish(4)
    }
}

typealias RxSchedulerBlockNoDelay = (Runnable) -> Disposable
typealias RxSchedulerBlockWithDelay = (Runnable, Long, TimeUnit) -> Disposable