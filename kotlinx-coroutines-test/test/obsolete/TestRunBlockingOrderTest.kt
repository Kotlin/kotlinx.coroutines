/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.obsolete

import junit.framework.TestCase.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.test.*
import org.junit.*
import java.util.concurrent.*
import kotlin.concurrent.*

class TestRunBlockingOrderTest : TestBase() {

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
                    expect(value + 1)
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
