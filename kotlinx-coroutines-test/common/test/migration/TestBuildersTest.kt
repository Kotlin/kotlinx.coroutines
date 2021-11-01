/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.test.*

@Suppress("DEPRECATION")
class TestBuildersTest {

    @Test
    fun scopeRunBlocking_passesDispatcher() {
        val scope = TestCoroutineScope()
        scope.runBlockingTest {
            assertSame(scope.coroutineContext[ContinuationInterceptor], coroutineContext[ContinuationInterceptor])
        }
    }

    @Test
    fun dispatcherRunBlocking_passesDispatcher() {
        val dispatcher = TestCoroutineDispatcher()
        dispatcher.runBlockingTest {
            assertSame(dispatcher, coroutineContext[ContinuationInterceptor])
        }
    }

    @Test
    fun scopeRunBlocking_advancesPreviousDelay() {
        val scope = TestCoroutineScope()
        val deferred = scope.async {
            delay(SLOW)
            3
        }

        scope.runBlockingTest {
            assertRunsFast {
                assertEquals(3, deferred.await())
            }
        }
    }

    @Test
    fun dispatcherRunBlocking_advancesPreviousDelay() {
        val dispatcher = TestCoroutineDispatcher()
        val scope = CoroutineScope(dispatcher)
        val deferred = scope.async {
            delay(SLOW)
            3
        }

        dispatcher.runBlockingTest {
            assertRunsFast {
                assertEquals(3, deferred.await())
            }
        }
    }

    @Test
    fun scopeRunBlocking_disablesImmediatelyOnExit() {
        val scope = TestCoroutineScope()
        scope.runBlockingTest {
            assertRunsFast {
                delay(SLOW)
            }
        }

        val deferred = scope.async {
            delay(SLOW)
            3
        }
        scope.runCurrent()
        assertTrue(deferred.isActive)

        scope.advanceUntilIdle()
        assertEquals(3, deferred.getCompleted())
    }

    @Test
    fun whenInAsync_runBlocking_nestsProperly() {
        // this is not a supported use case, but it is possible so ensure it works

        val dispatcher = TestCoroutineDispatcher()
        val scope = TestCoroutineScope(dispatcher)
        val deferred = scope.async {
            delay(1_000)
            var retval = 2
            runBlockingTest {
                delay(1_000)
                retval++
            }
            retval
        }

        scope.advanceTimeBy(1_000)
        scope.launch {
            assertRunsFast {
                assertEquals(3, deferred.getCompleted())
            }
        }
        scope.runCurrent() // execute the launch without changing to immediate dispatch (testing internals)
        scope.cleanupTestCoroutines()
    }

    @Test
    fun whenInRunBlocking_runBlockingTest_nestsProperly() {
        // this is not a supported use case, but it is possible so ensure it works

        val scope = TestCoroutineScope()
        var calls = 0

        scope.runBlockingTest {
            delay(1_000)
            calls++
            runBlockingTest {
                val job = launch {
                    delay(1_000)
                    calls++
                }
                assertTrue(job.isActive)
                advanceUntilIdle()
                assertFalse(job.isActive)
                calls++
            }
            ++calls
        }

        assertEquals(4, calls)
    }
}