/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.test.*

@Suppress("DEPRECATION")
class TestCoroutineDispatcherTest {
    @Test
    fun whenDispatcherPaused_doesNotAutoProgressCurrent() {
        val subject = TestCoroutineDispatcher()
        subject.pauseDispatcher()
        val scope = CoroutineScope(subject)
        var executed = 0
        scope.launch {
            executed++
        }
        assertEquals(0, executed)
    }

    @Test
    fun whenDispatcherResumed_doesAutoProgressCurrent() {
        val subject = TestCoroutineDispatcher()
        val scope = CoroutineScope(subject)
        var executed = 0
        scope.launch {
            executed++
        }

        assertEquals(1, executed)
    }

    @Test
    fun whenDispatcherResumed_doesNotAutoProgressTime() {
        val subject = TestCoroutineDispatcher()
        val scope = CoroutineScope(subject)
        var executed = 0
        scope.launch {
            delay(1_000)
            executed++
        }

        assertEquals(0, executed)
        subject.advanceUntilIdle()
        assertEquals(1, executed)
    }

    @Test
    fun whenDispatcherPaused_thenResume_itDoesDispatchCurrent() {
        val subject = TestCoroutineDispatcher()
        subject.pauseDispatcher()
        val scope = CoroutineScope(subject)
        var executed = 0
        scope.launch {
            executed++
        }

        assertEquals(0, executed)
        subject.resumeDispatcher()
        assertEquals(1, executed)
    }

    @Test
    fun whenDispatcherHasUncompletedCoroutines_itThrowsErrorInCleanup() {
        val subject = TestCoroutineDispatcher()
        subject.pauseDispatcher()
        val scope = CoroutineScope(subject)
        scope.launch {
            delay(1_000)
        }
        assertFailsWith<UncompletedCoroutinesError> { subject.cleanupTestCoroutines() }
    }

}