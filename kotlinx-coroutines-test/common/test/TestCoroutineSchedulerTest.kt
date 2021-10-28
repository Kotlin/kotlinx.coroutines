/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.test.*

class TestCoroutineSchedulerTest {
    /** Tests that `TestCoroutineScheduler` attempts to detect if there are several instances of it. */
    @Test
    fun testContextElement() = runBlockingTest {
        assertFailsWith<IllegalStateException> {
            withContext(TestCoroutineDispatcher()) {
            }
        }
    }

    /** Tests that, as opposed to [DelayController.advanceTimeBy] or [TestCoroutineScope.advanceTimeBy],
     * [TestCoroutineScheduler.advanceTimeBy] doesn't run the tasks scheduled at the target moment. */
    @Test
    fun testAdvanceTimeByDoesNotRunCurrent() = runBlockingTest {
        var entered = false
        launch {
            delay(15)
            entered = true
        }
        testScheduler.advanceTimeBy(15)
        assertFalse(entered)
        testScheduler.runCurrent()
        assertTrue(entered)
    }

    /** Tests that [TestCoroutineScheduler.advanceTimeBy] doesn't accept negative delays. */
    @Test
    fun testAdvanceTimeByWithNegativeDelay() {
        val scheduler = TestCoroutineScheduler()
        assertFailsWith<IllegalArgumentException> {
            scheduler.advanceTimeBy(-1)
        }
    }

    /** Tests that if [TestCoroutineScheduler.advanceTimeBy] encounters an arithmetic overflow, all the tasks scheduled
     * until the moment [Long.MAX_VALUE] get run. */
    @Test
    fun testAdvanceTimeByEnormousDelays() = runBlockingTest {
        val initialDelay = 10L
        delay(initialDelay)
        assertEquals(initialDelay, currentTime)
        var enteredInfinity = false
        launch {
            delay(Long.MAX_VALUE - 1) // delay(Long.MAX_VALUE) does nothing
            assertEquals(Long.MAX_VALUE, currentTime)
            enteredInfinity = true
        }
        var enteredNearInfinity = false
        launch {
            delay(Long.MAX_VALUE - initialDelay - 1)
            assertEquals(Long.MAX_VALUE - 1, currentTime)
            enteredNearInfinity = true
        }
        testScheduler.advanceTimeBy(Long.MAX_VALUE)
        assertFalse(enteredInfinity)
        assertTrue(enteredNearInfinity)
        assertEquals(Long.MAX_VALUE, currentTime)
        testScheduler.runCurrent()
        assertTrue(enteredInfinity)
    }

    /** Tests the basic functionality of [TestCoroutineScheduler.advanceTimeBy]. */
    @Test
    fun testAdvanceTimeBy() = assertRunsFast {
        val scheduler = TestCoroutineScheduler()
        val scope = TestCoroutineScope(scheduler)
        var stage = 1
        scope.launch {
            delay(1_000)
            assertEquals(1_000, scheduler.currentTime)
            stage = 2
            delay(500)
            assertEquals(1_500, scheduler.currentTime)
            stage = 3
            delay(501)
            assertEquals(2_001, scheduler.currentTime)
            stage = 4
        }
        assertEquals(1, stage)
        assertEquals(0, scheduler.currentTime)
        scheduler.advanceTimeBy(2_000)
        assertEquals(3, stage)
        assertEquals(2_000, scheduler.currentTime)
        scheduler.advanceTimeBy(2)
        assertEquals(4, stage)
        assertEquals(2_002, scheduler.currentTime)
        scope.cleanupTestCoroutines()
    }

    /** Tests the basic functionality of [TestCoroutineScheduler.runCurrent]. */
    @Test
    fun testRunCurrent() = runBlockingTest {
        var stage = 0
        launch {
            delay(1)
            ++stage
            delay(1)
            stage += 10
        }
        launch {
            delay(1)
            ++stage
            delay(1)
            stage += 10
        }
        testScheduler.advanceTimeBy(1)
        assertEquals(0, stage)
        runCurrent()
        assertEquals(2, stage)
        testScheduler.advanceTimeBy(1)
        assertEquals(2, stage)
        runCurrent()
        assertEquals(22, stage)
    }

    /** Tests that [TestCoroutineScheduler.runCurrent] will not run new tasks after the current time has advanced. */
    @Test
    fun testRunCurrentNotDrainingQueue() = assertRunsFast {
        val scheduler = TestCoroutineScheduler()
        val scope = TestCoroutineScope(scheduler)
        var stage = 1
        scope.launch {
            delay(SLOW)
            launch {
                delay(SLOW)
                stage = 3
            }
            scheduler.advanceTimeBy(SLOW)
            stage = 2
        }
        scheduler.advanceTimeBy(SLOW)
        assertEquals(1, stage)
        scheduler.runCurrent()
        assertEquals(2, stage)
        scheduler.runCurrent()
        assertEquals(3, stage)
    }

    /** Tests that [TestCoroutineScheduler.advanceUntilIdle] doesn't hang when itself running in a scheduler task. */
    @Test
    fun testNestedAdvanceUntilIdle() = assertRunsFast {
        val scheduler = TestCoroutineScheduler()
        val scope = TestCoroutineScope(scheduler)
        var executed = false
        scope.launch {
            launch {
                delay(SLOW)
                executed = true
            }
            scheduler.advanceUntilIdle()
        }
        scheduler.advanceUntilIdle()
        assertTrue(executed)
    }

    /** Tests [yield] scheduling tasks for future execution and not executing immediately. */
    @Test
    fun testYield() {
        val scope = TestCoroutineScope()
        var stage = 0
        scope.launch {
            yield()
            assertEquals(1, stage)
            stage = 2
        }
        scope.launch {
            yield()
            assertEquals(2, stage)
            stage = 3
        }
        assertEquals(0, stage)
        stage = 1
        scope.runCurrent()
    }
}
