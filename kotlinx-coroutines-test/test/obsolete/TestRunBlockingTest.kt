/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.obsolete

import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import java.lang.IllegalStateException
import kotlin.coroutines.*
import kotlin.test.*

class TestRunBlockingTest {

    @Test(expected = java.lang.IllegalArgumentException::class)
    fun runBlockingTestBuilder_throwsOnBadDispatcher() {
        runBlockingTest(newSingleThreadContext("name")) {

        }
    }

    @Test(expected = java.lang.IllegalArgumentException::class)
    fun runBlockingTestBuilder_throwsOnBadHandler() {
        runBlockingTest(CoroutineExceptionHandler { _, _ -> Unit }) {

        }
    }

    @Test
    fun pauseDispatcher_disablesAutoAdvance_forCurrent() = runBlockingTest {
        var mutable = 0
        pauseDispatcher {
            launch {
                mutable++
            }
            assertEquals(0, mutable)
            runCurrent()
            assertEquals(1, mutable)
        }
    }

    @Test
    fun pauseDispatcher_disablesAutoAdvance_forDelay() = runBlockingTest {
        var mutable = 0
        pauseDispatcher {
            launch {
                mutable++
                delay(SLOW)
                mutable++
            }
            assertEquals(0, mutable)
            runCurrent()
            assertEquals(1, mutable)
            advanceTimeBy(SLOW)
            assertEquals(2, mutable)
        }
    }

    @Test
    fun pauseDispatcher_withDelay_resumesAfterPause() = runBlockingTest {
        var mutable = 0
        assertRunsFast {
            pauseDispatcher {
                delay(1_000)
                mutable++
            }
        }
        assertEquals(1, mutable)
    }


    @Test(expected = IllegalAccessError::class)
    fun testWithTestContextThrowingAnAssertionError() = runBlockingTest {
        val expectedError = IllegalAccessError("hello")

        launch {
            throw expectedError
        }

        // don't rethrow or handle the exception
    }

    @Test(expected = IllegalAccessError::class)
    fun testExceptionHandlingWithLaunch() = runBlockingTest {
        val expectedError = IllegalAccessError("hello")

        launch {
            throw expectedError
        }
    }

    @Test(expected = IllegalAccessError::class)
    fun testExceptions_notThrownImmediately() = runBlockingTest {
        val expectedException = IllegalAccessError("hello")
        val result = runCatching {
            launch {
                throw expectedException
            }
        }
        runCurrent()
        assertEquals(true, result.isSuccess)
    }


    private val exceptionHandler = TestCoroutineExceptionHandler()

    @Test
    fun testPartialContextOverride() = runBlockingTest(CoroutineName("named")) {
        assertEquals(CoroutineName("named"), coroutineContext[CoroutineName])
        assertNotNull(coroutineContext[CoroutineExceptionHandler])
        assertNotSame(coroutineContext[CoroutineExceptionHandler], exceptionHandler)
    }

    @Test(expected = IllegalArgumentException::class)
    fun testPartialDispatcherOverride() = runBlockingTest(Dispatchers.Unconfined) {
        fail("Unreached")
    }

    @Test
    fun testOverrideExceptionHandler() = runBlockingTest(exceptionHandler) {
        assertSame(coroutineContext[CoroutineExceptionHandler], exceptionHandler)
    }

    @Test(expected = IllegalArgumentException::class)
    fun testOverrideExceptionHandlerError() =
        runBlockingTest(CoroutineExceptionHandler { _, _ -> }) {
            fail("Unreached")
        }
}
