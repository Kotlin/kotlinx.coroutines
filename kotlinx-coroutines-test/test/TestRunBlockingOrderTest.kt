/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import junit.framework.TestCase.assertEquals
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.junit.*
import java.util.concurrent.Executors
import kotlin.concurrent.thread

class TestRunBlockingOrderTest : TestBase() {
    @Test
    fun testLaunchImmediate() = runBlockingTest {
        expect(1)
        launch {
            expect(2)
        }
        finish(3)
    }

    @Test
    fun testYield() = runBlockingTest {
        expect(1)
        launch {
            expect(2)
            yield()
            finish(4)
        }
        expect(3)
    }

    @Test
    fun testLaunchWithDelayCompletes() = runBlockingTest {
        expect(1)
        launch {
            delay(100)
            finish(3)
        }
        expect(2)
    }

    @Test
    fun testLaunchDelayOrdered() = runBlockingTest {
        expect(1)
        launch {
            delay(200) // long delay
            finish(4)
        }
        launch  {
            delay(100) // shorter delay
            expect(3)
        }
        expect(2)
    }

    @Test
    fun testInfiniteDelay() = runBlockingTest {
        expect(1)
        delay(100) // move time forward a bit some that naive time + delay gives an overflow
        launch {
            delay(Long.MAX_VALUE) // infinite delay
            finish(4)
        }
        launch  {
            delay(100) // short delay
            expect(3)
        }
        expect(2)
    }

    @Test
    fun testNewThread_inSuspendCancellableCoroutine() = runBlockingTest {
        expect(1)
        suspendCancellableCoroutine<Unit> { cont ->
            expect(2)
            thread {
                expect(3)
                cont.resume(Unit) { Unit }
            }
        }
        finish(4)
    }

    @Test
    fun testWithDelayInOtherDispatcher_passesWhenDelayIsShort() = runBlockingTest {
        expect(1)
        withContext(Dispatchers.IO) {
            delay(1)
            expect(2)
        }
        finish(3)
    }

    @Test
    fun testThrows_throws() {
        val expected = IllegalStateException("expected")
        val result = runCatching {
            expect(1)
            runBlockingTest {
                expect(2)
                throw expected
            }
        }
        finish(3)
        assertEquals(expected, result.exceptionOrNull())
    }

    @Test
    fun testSuspendForever_fails() {
        val uncompleted = CompletableDeferred<Unit>()
        val result = runCatching {
            expect(1)
            runBlockingTest(waitForOtherDispatchers = 0L) {
                expect(2)
                uncompleted.await()
            }
        }
        finish(3)
        assertEquals(true, result.isFailure)
    }

    @Test
    fun testAdvanceUntilIdle_inRunBlocking() = runBlockingTest {
        expect(1)
        assertRunsFast {
            advanceUntilIdle()   // ensure this doesn't block forever
        }
        finish(2)
    }

    @Test
    fun testComplexDispatchFromOtherDispatchersOverTime_completes() {
        val otherDispatcher = Executors.newSingleThreadExecutor().asCoroutineDispatcher()

        val max = 10

        val numbersFromOtherDispatcherWithDelays = flow<Int> {
            var current = 0
            while (current < max) {
                delay(1)
                emit(++current)
            }
        }.flowOn(otherDispatcher)

        try {
            runBlockingTest {
                numbersFromOtherDispatcherWithDelays.collect { value ->
                    expect(value)
                }
                expect(max + 1)
            }
        } finally {
            otherDispatcher.close()
        }
        finish(max + 2)
    }

    @Test
    fun testComplexDispatchFromOtherDispatchersOverTime_withPasuedTestDispatcher_completes() {
        val otherDispatcher = Executors.newSingleThreadExecutor().asCoroutineDispatcher()

        val max = 10

        val numbersFromOtherDispatcherWithDelays = flow { for(x in 1..max) { emit(x) } }
                .buffer(0)
                .delayEach(1)
                .flowOn(otherDispatcher)

        otherDispatcher.use {
            runBlockingTest {
                pauseDispatcher()
                numbersFromOtherDispatcherWithDelays.collect { value ->
                    expect(value)
                }
                expect(max + 1)
            }
        }
        finish(max + 2)
    }

    @Test
    fun testDispatchFromOtherDispatch_triggersInternalDispatch() {
        val otherDispatcher = Executors.newSingleThreadExecutor().asCoroutineDispatcher()

        val numbersFromOtherDispatcherWithDelays = flow { emit(1) }
                .delayEach(1)
                .buffer(0)
                .flowOn(otherDispatcher)

        otherDispatcher.use {
            runBlockingTest {
                numbersFromOtherDispatcherWithDelays.collect { value ->
                    expect(value)
                    launch {
                        expect(2)
                    }
                }
                expect(3)
            }
        }
        finish(4)
    }

    @Test
    fun testDispatchFromOtherDispatch_triggersInternalDispatch_withDelay() {
        val otherDispatcher = Executors.newSingleThreadExecutor().asCoroutineDispatcher()

        val max = 10

        val numbersFromOtherDispatcherWithDelays = flow { for(x in 1..max) { emit(x)} }
                .filter { it % 2 == 1 }
                .delayEach(1)
                .buffer(0)
                .flowOn(otherDispatcher)

        otherDispatcher.use {
            runBlockingTest {
                numbersFromOtherDispatcherWithDelays.collect { value ->
                    expect(value)
                    delay(1)
                    expect (value + 1)
                }
                delay(1)
                expect(max + 1)
            }
        }
        finish(max + 2)
    }

    @Test
    fun whenWaitConfig_timesOut_getExceptionWithMessage() {
        expect(1)
        val uncompleted = CompletableDeferred<Unit>()
        val result = runCatching {
            runBlockingTest(waitForOtherDispatchers = 1L) {
                withContext(Dispatchers.IO) {
                    finish(2)
                    uncompleted.await()
                }
            }
        }
        val hasDetailedError = result.exceptionOrNull()?.message?.contains("may be empty")
        assertEquals(true, hasDetailedError)
        uncompleted.cancel()
    }

    @Test
    fun whenCoroutineStartedInScope_doesntLeakOnAnotherDispatcher() {
        var job: Job? = null
        runBlockingTest {
            expect(1)
            job = launch(Dispatchers.IO) {
                delay(1)
                expect(3)
            }
            expect(2)
        }
        assertEquals(true, job?.isCompleted)
        finish(4)
    }

    @Test
    fun whenDispatcherPaused_runBlocking_dispatchesToTestThread() {
        val thread = Thread.currentThread()
        runBlockingTest {
            pauseDispatcher()
            withContext(Dispatchers.IO) {
                expect(1)
                delay(1)
                expect(2)
            }
            assertEquals(thread, Thread.currentThread())
            finish(3)
        }
    }

    @Test
    fun whenDispatcherResumed_runBlocking_dispatchesImmediatelyOnIO() {
        var thread: Thread? = null
        runBlockingTest {
            resumeDispatcher()
            withContext(Dispatchers.IO) {
                expect(1)
                delay(1)
                expect(2)
                thread = Thread.currentThread()
            }
            assertEquals(thread, Thread.currentThread())
            finish(3)
        }
    }

    @Test
    fun whenDispatcherRunning_doesntProgressDelays_inLaunchBody() {
        var state = 0
        fun CoroutineScope.subject() = launch {
            state = 1
            delay(1000)
            state = 2
        }

        runBlockingTest {
            subject()

            assertEquals(1, state)

            advanceTimeBy(1000)

            assertEquals(2, state)
        }
    }
}
