/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class TestCoroutineDispatcherTest {
    @Test
    fun whenStringCalled_itReturnsString() {
        val subject = TestCoroutineDispatcher()
        assertEquals("TestCoroutineDispatcher[currentTime=0ms, queued=0]", subject.toString())
    }

    @Test
    fun whenStringCalled_itReturnsCurrentTime() {
        val subject = TestCoroutineDispatcher()
        subject.advanceTimeBy(1000)
        assertEquals("TestCoroutineDispatcher[currentTime=1000ms, queued=0]", subject.toString())
    }

    @Test
    fun whenStringCalled_itShowsQueuedJobs() {
        val subject = TestCoroutineDispatcher()
        val scope = TestCoroutineScope(subject)
        scope.pauseDispatcher()
        scope.launch {
            delay(1_000)
        }
        assertEquals("TestCoroutineDispatcher[currentTime=0ms, queued=1]", subject.toString())
        scope.advanceTimeBy(50)
        assertEquals("TestCoroutineDispatcher[currentTime=50ms, queued=1]", subject.toString())
        scope.advanceUntilIdle()
        assertEquals("TestCoroutineDispatcher[currentTime=1000ms, queued=0]", subject.toString())
    }

    @Test
    fun whenDispatcherPaused_doesntAutoProgressCurrent() {
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

    @Test(expected = UncompletedCoroutinesError::class)
    fun whenDispatcherHasUncompletedCoroutines_itThrowsErrorInCleanup() {
        val subject = TestCoroutineDispatcher()
        subject.pauseDispatcher()
        val scope = CoroutineScope(subject)
        scope.launch {
            delay(1_000)
        }
        subject.cleanupTestCoroutines()
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
}