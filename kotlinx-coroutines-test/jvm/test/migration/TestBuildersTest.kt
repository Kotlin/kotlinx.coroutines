package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import kotlin.coroutines.*
import kotlin.test.*

@Suppress("DEPRECATION", "DEPRECATION_ERROR")
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
