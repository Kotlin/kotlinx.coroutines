/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import kotlin.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

class MultithreadingTest {

    @Test
    fun incorrectlyCalledRunBlocking_doesNotHaveSameInterceptor() = runBlockingTest {
        // this code is an error as a production test, please do not use this as an example

        // this test exists to document this error condition, if it's possible to make this code work please update
        val outerInterceptor = coroutineContext[ContinuationInterceptor]
        // runBlocking always requires an argument to pass the context in tests
        runBlocking {
            assertNotSame(coroutineContext[ContinuationInterceptor], outerInterceptor)
        }
    }

    @Test
    fun testSingleThreadExecutor() = runBlocking {
        val mainThread = Thread.currentThread()
        Dispatchers.setMain(Dispatchers.Unconfined)
        newSingleThreadContext("testSingleThread").use { threadPool ->
            withContext(Dispatchers.Main) {
                assertSame(mainThread, Thread.currentThread())
            }

            Dispatchers.setMain(threadPool)
            withContext(Dispatchers.Main) {
                assertNotSame(mainThread, Thread.currentThread())
            }
            assertSame(mainThread, Thread.currentThread())

            withContext(Dispatchers.Main.immediate) {
                assertNotSame(mainThread, Thread.currentThread())
            }
            assertSame(mainThread, Thread.currentThread())

            Dispatchers.setMain(Dispatchers.Unconfined)
            withContext(Dispatchers.Main.immediate) {
                assertSame(mainThread, Thread.currentThread())
            }
            assertSame(mainThread, Thread.currentThread())
        }
    }

    @Test
    fun whenDispatchCalled_runsOnCurrentThread() {
        val currentThread = Thread.currentThread()
        val subject = TestCoroutineDispatcher()
        val scope = TestCoroutineScope(subject)

        val deferred = scope.async(Dispatchers.Default) {
            withContext(subject) {
                assertNotSame(currentThread, Thread.currentThread())
                3
            }
        }

        runBlocking {
            // just to ensure the above code terminates
            assertEquals(3, deferred.await())
        }
    }

    @Test
    fun whenAllDispatchersMocked_runsOnSameThread() {
        val currentThread = Thread.currentThread()
        val subject = TestCoroutineDispatcher()
        val scope = TestCoroutineScope(subject)

        val deferred = scope.async(subject) {
            withContext(subject) {
                assertSame(currentThread, Thread.currentThread())
                3
            }
        }

        runBlocking {
            // just to ensure the above code terminates
            assertEquals(3, deferred.await())
        }
    }

    /** Tests that resuming the coroutine of [runTest] asynchronously in reasonable time succeeds. */
    @Test
    fun testResumingFromAnotherThread() = runTest {
        suspendCancellableCoroutine<Unit> { cont ->
            thread {
                Thread.sleep(10)
                cont.resume(Unit)
            }
        }
    }

    /** Tests that [StandardTestDispatcher] is not executed in-place but confined to the thread in which the
     * virtual time control happens. */
    @Test
    fun testStandardTestDispatcherIsConfined(): Unit = runBlocking {
        val scheduler = TestCoroutineScheduler()
        val initialThread = Thread.currentThread()
        val job = launch(StandardTestDispatcher(scheduler)) {
            assertEquals(initialThread, Thread.currentThread())
            withContext(Dispatchers.IO) {
                val ioThread = Thread.currentThread()
                assertNotSame(initialThread, ioThread)
            }
            assertEquals(initialThread, Thread.currentThread())
        }
        scheduler.advanceUntilIdle()
        while (job.isActive) {
            scheduler.receiveDispatchEvent()
            scheduler.advanceUntilIdle()
        }
    }
}
