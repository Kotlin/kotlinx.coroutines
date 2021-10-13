/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*
import kotlin.test.*

class RunTestTest {

    /** Tests that [withContext] that sends work to other threads works in [runTest]. */
    @Test
    fun testWithContextDispatching() = runTest {
        var counter = 0
        withContext(Dispatchers.Default) {
            counter += 1
        }
        assertEquals(counter, 1)
    }

    /** Tests that joining [GlobalScope.launch] works in [runTest]. */
    @Test
    fun testJoiningForkedJob() = runTest {
        var counter = 0
        val job = GlobalScope.launch {
            counter += 1
        }
        job.join()
        assertEquals(counter, 1)
    }

    /** Tests [suspendCoroutine] not failing [runTest]. */
    @Test
    fun testSuspendCoroutine() = runTest {
        val answer = suspendCoroutine<Int> {
            it.resume(42)
        }
        assertEquals(42, answer)
    }

    /** Tests that [runTest] attempts to detect it being run inside another [runTest] and failing in such scenarios. */
    @Test
    fun testNestedRunTestForbidden() = runTest {
        assertFailsWith<IllegalStateException> {
            runTest { }
        }
    }

    /** Tests that even the dispatch timeout of `0` is fine if all the dispatches go through the same scheduler. */
    @Test
    fun testRunTestWithZeroTimeoutWithControlledDispatches() = runTest(dispatchTimeoutMs = 0) {
        // below is some arbitrary concurrent code where all dispatches go through the same scheduler.
        launch {
            delay(2000)
        }
        val deferred = async {
            val job = launch(TestCoroutineDispatcher(testScheduler)) {
                launch {
                    delay(500)
                }
                delay(1000)
            }
            job.join()
        }
        deferred.await()
    }

    /** Tests that a dispatch timeout of `0` will fail the test if there are some dispatches outside the scheduler. */
    @Test
    fun testRunTestWithZeroTimeoutWithUncontrolledDispatches() = testResultMap({ fn ->
        assertFailsWith<UncompletedCoroutinesError> { fn() }
    }) {
        runTest(dispatchTimeoutMs = 0) {
            withContext(Dispatchers.Default) {
                delay(10)
                3
            }
            throw IllegalStateException("shouldn't be reached")
        }
    }

    /** Tests that too low of a dispatch timeout causes crashes. */
    @Test
    @Ignore // TODO: timeout leads to `Cannot execute task because event loop was shut down` on Native
    fun testRunTestWithSmallTimeout() = testResultMap({ fn ->
        assertFailsWith<UncompletedCoroutinesError> { fn() }
    }) {
        runTest(dispatchTimeoutMs = 100) {
            withContext(Dispatchers.Default) {
                delay(10000)
                3
            }
            throw RuntimeException("shouldn't be reached")
        }
    }

    /** Tests that too low of a dispatch timeout causes crashes. */
    @Test
    fun testRunTestWithLargeTimeout() = runTest(dispatchTimeoutMs = 5000) {
        withContext(Dispatchers.Default) {
            delay(50)
        }
    }

    /** Tests uncaught exceptions taking priority over dispatch timeout in error reports. */
    @Test
    @Ignore // TODO: timeout leads to `Cannot execute task because event loop was shut down` on Native
    fun testRunTestTimingOutAndThrowing() = testResultMap({ fn ->
        assertFailsWith<IllegalArgumentException> { fn() }
    }) {
        runTest(dispatchTimeoutMs = 1) {
            coroutineContext[CoroutineExceptionHandler]!!.handleException(coroutineContext, IllegalArgumentException())
            withContext(Dispatchers.Default) {
                delay(10000)
                3
            }
            throw RuntimeException("shouldn't be reached")
        }
    }

    /** Tests that passing invalid contexts to [runTest] causes it to fail (on JS, without forking). */
    @Test
    fun testRunTestWithIllegalContext() {
        for (ctx in TestCoroutineScopeTest.invalidContexts) {
            assertFailsWith<IllegalArgumentException> {
                runTest(ctx) { }
            }
        }
    }

    /** Tests that throwing exceptions in [runTest] fails the test with them. */
    @Test
    fun testThrowingInRunTestBody() = testResultMap({
        assertFailsWith<RuntimeException> { it() }
    }) {
        runTest {
            throw RuntimeException()
        }
    }

    /** Tests that throwing exceptions in pending tasks [runTest] fails the test with them. */
    @Test
    fun testThrowingInRunTestPendingTask() = testResultMap({
        assertFailsWith<RuntimeException> { it() }
    }) {
        runTest {
            launch {
                delay(SLOW)
                throw RuntimeException()
            }
        }
    }

    @Test
    fun reproducer2405() = runTest {
        val dispatcher = StandardTestDispatcher(testScheduler)
        var collectedError = false
        withContext(dispatcher) {
            flow { emit(1) }
                .combine(
                    flow<String> { throw IllegalArgumentException() }
                ) { int, string -> int.toString() + string }
                .catch { emit("error") }
                .collect {
                    assertEquals("error", it)
                    collectedError = true
                }
        }
        assertTrue(collectedError)
    }

}
