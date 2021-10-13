/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.test.*

class TestCoroutineSchedulerTest {
    /** Tests that `TestCoroutineScheduler` attempts to detect if there are several instances of it. */
    @Test
    fun testContextElement() {
        runBlockingTest {
            assertFailsWith<IllegalStateException> {
                withContext(TestCoroutineDispatcher()) {
                }
            }
        }
    }

    /** Tests that, as opposed to [DelayController.advanceTimeBy] or [TestCoroutineScope.advanceTimeBy],
     * [TestCoroutineScheduler.advanceTimeBy] doesn't run the tasks scheduled at the target moment. */
    @Test
    fun testAdvanceTimeByDoesNotRunCurrent() {
        val dispatcher = TestCoroutineDispatcher()
        dispatcher.runBlockingTest {
            dispatcher.pauseDispatcher {
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
        }
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
    fun testAdvanceTimeByEnormousDelays() {
        val dispatcher = TestCoroutineDispatcher()
        dispatcher.runBlockingTest {
            dispatcher.pauseDispatcher {
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
        }
    }
}
