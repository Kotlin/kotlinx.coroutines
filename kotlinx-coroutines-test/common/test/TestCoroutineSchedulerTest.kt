/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.test.*
import kotlin.time.*
import kotlin.time.Duration.Companion.seconds
import kotlin.time.Duration.Companion.milliseconds

class TestCoroutineSchedulerTest {
    /** Tests that `TestCoroutineScheduler` attempts to detect if there are several instances of it. */
    @Test
    fun testContextElement() = runTest {
        assertFailsWith<IllegalStateException> {
            withContext(StandardTestDispatcher()) {
            }
        }
    }

    /** Tests that, as opposed to [DelayController.advanceTimeBy] or [TestCoroutineScope.advanceTimeBy],
     * [TestCoroutineScheduler.advanceTimeBy] doesn't run the tasks scheduled at the target moment. */
    @Test
    fun testAdvanceTimeByDoesNotRunCurrent() = runTest {
        var entered = false
        launch {
            delay(15)
            entered = true
        }
        testScheduler.advanceTimeBy(15.milliseconds)
        assertFalse(entered)
        testScheduler.runCurrent()
        assertTrue(entered)
    }

    /** Tests that [TestCoroutineScheduler.advanceTimeBy] doesn't accept negative delays. */
    @Test
    fun testAdvanceTimeByWithNegativeDelay() {
        val scheduler = TestCoroutineScheduler()
        assertFailsWith<IllegalArgumentException> {
            scheduler.advanceTimeBy((-1).milliseconds)
        }
    }

    /** Tests that if [TestCoroutineScheduler.advanceTimeBy] encounters an arithmetic overflow, all the tasks scheduled
     * until the moment [Long.MAX_VALUE] get run. */
    @Test
    fun testAdvanceTimeByEnormousDelays() = forTestDispatchers {
        assertRunsFast {
            with (TestScope(it)) {
                launch {
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
                    testScheduler.advanceTimeBy(Duration.INFINITE)
                    assertFalse(enteredInfinity)
                    assertTrue(enteredNearInfinity)
                    assertEquals(Long.MAX_VALUE, currentTime)
                    testScheduler.runCurrent()
                    assertTrue(enteredInfinity)
                }
                testScheduler.advanceUntilIdle()
            }
        }
    }

    /** Tests the basic functionality of [TestCoroutineScheduler.advanceTimeBy]. */
    @Test
    fun testAdvanceTimeBy() = runTest {
        assertRunsFast {
            var stage = 1
            launch {
                delay(1_000)
                assertEquals(1_000, currentTime)
                stage = 2
                delay(500)
                assertEquals(1_500, currentTime)
                stage = 3
                delay(501)
                assertEquals(2_001, currentTime)
                stage = 4
            }
            assertEquals(1, stage)
            assertEquals(0, currentTime)
            advanceTimeBy(2.seconds)
            assertEquals(3, stage)
            assertEquals(2_000, currentTime)
            advanceTimeBy(2.milliseconds)
            assertEquals(4, stage)
            assertEquals(2_002, currentTime)
        }
    }

    /** Tests the basic functionality of [TestCoroutineScheduler.runCurrent]. */
    @Test
    fun testRunCurrent() = runTest {
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
        testScheduler.advanceTimeBy(1.milliseconds)
        assertEquals(0, stage)
        runCurrent()
        assertEquals(2, stage)
        testScheduler.advanceTimeBy(1.milliseconds)
        assertEquals(2, stage)
        runCurrent()
        assertEquals(22, stage)
    }

    /** Tests that [TestCoroutineScheduler.runCurrent] will not run new tasks after the current time has advanced. */
    @Test
    fun testRunCurrentNotDrainingQueue() = forTestDispatchers {
        assertRunsFast {
            val scheduler = it.scheduler
            val scope = TestScope(it)
            var stage = 1
            scope.launch {
                delay(SLOW)
                launch {
                    delay(SLOW)
                    stage = 3
                }
                scheduler.advanceTimeBy(SLOW.milliseconds)
                stage = 2
            }
            scheduler.advanceTimeBy(SLOW.milliseconds)
            assertEquals(1, stage)
            scheduler.runCurrent()
            assertEquals(2, stage)
            scheduler.runCurrent()
            assertEquals(3, stage)
        }
    }

    /** Tests that [TestCoroutineScheduler.advanceUntilIdle] doesn't hang when itself running in a scheduler task. */
    @Test
    fun testNestedAdvanceUntilIdle() = forTestDispatchers {
        assertRunsFast {
            val scheduler = it.scheduler
            val scope = TestScope(it)
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
    }

    /** Tests [yield] scheduling tasks for future execution and not executing immediately. */
    @Test
    fun testYield() = forTestDispatchers {
        val scope = TestScope(it)
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

    /** Tests that dispatching the delayed tasks is ordered by their waking times. */
    @Test
    fun testDelaysPriority() = forTestDispatchers {
        val scope = TestScope(it)
        var lastMeasurement = 0L
        fun checkTime(time: Long) {
            assertTrue(lastMeasurement < time)
            assertEquals(time, scope.currentTime)
            lastMeasurement = scope.currentTime
        }
        scope.launch {
            launch {
                delay(100)
                checkTime(100)
                val deferred = async {
                    delay(70)
                    checkTime(170)
                }
                delay(1)
                checkTime(101)
                deferred.await()
                delay(1)
                checkTime(171)
            }
            launch {
                delay(200)
                checkTime(200)
            }
            launch {
                delay(150)
                checkTime(150)
                delay(22)
                checkTime(172)
            }
            delay(201)
        }
        scope.advanceUntilIdle()
        checkTime(201)
    }

    private fun TestScope.checkTimeout(
        timesOut: Boolean, timeoutMillis: Long = SLOW, block: suspend () -> Unit
    ) = assertRunsFast {
        var caughtException = false
        asSpecificImplementation().enter()
        launch {
            try {
                withTimeout(timeoutMillis) {
                    block()
                }
            } catch (e: TimeoutCancellationException) {
                caughtException = true
            }
        }
        advanceUntilIdle()
        throwAll(null, asSpecificImplementation().legacyLeave())
        if (timesOut)
            assertTrue(caughtException)
        else
            assertFalse(caughtException)
    }

    /** Tests that timeouts get triggered. */
    @Test
    fun testSmallTimeouts() = forTestDispatchers {
        val scope = TestScope(it)
        scope.checkTimeout(true) {
            val half = SLOW / 2
            delay(half)
            delay(SLOW - half)
        }
    }

    /** Tests that timeouts don't get triggered if the code finishes in time. */
    @Test
    fun testLargeTimeouts() = forTestDispatchers {
        val scope = TestScope(it)
        scope.checkTimeout(false) {
            val half = SLOW / 2
            delay(half)
            delay(SLOW - half - 1)
        }
    }

    /** Tests that timeouts get triggered if the code fails to finish in time asynchronously. */
    @Test
    fun testSmallAsynchronousTimeouts() = forTestDispatchers {
        val scope = TestScope(it)
        val deferred = CompletableDeferred<Unit>()
        scope.launch {
            val half = SLOW / 2
            delay(half)
            delay(SLOW - half)
            deferred.complete(Unit)
        }
        scope.checkTimeout(true) {
            deferred.await()
        }
    }

    /** Tests that timeouts don't get triggered if the code finishes in time, even if it does so asynchronously. */
    @Test
    fun testLargeAsynchronousTimeouts() = forTestDispatchers {
        val scope = TestScope(it)
        val deferred = CompletableDeferred<Unit>()
        scope.launch {
            val half = SLOW / 2
            delay(half)
            delay(SLOW - half - 1)
            deferred.complete(Unit)
        }
        scope.checkTimeout(false) {
            deferred.await()
        }
    }

    @Test
    @ExperimentalTime
    fun testAdvanceTimeSource() = runTest {
        val expected = 1.seconds
        val actual = testTimeSource.measureTime {
            delay(expected)
        }
        assertEquals(expected, actual)
    }

    private fun forTestDispatchers(block: (TestDispatcher) -> Unit): Unit =
        @Suppress("DEPRECATION")
        listOf(
            StandardTestDispatcher(),
            UnconfinedTestDispatcher()
        ).forEach {
            try {
                block(it)
            } catch (e: Throwable) {
                throw RuntimeException("Test failed for dispatcher $it", e)
            }
        }
}
