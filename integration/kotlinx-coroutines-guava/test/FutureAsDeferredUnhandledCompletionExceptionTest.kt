/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.guava

import com.google.common.util.concurrent.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class FutureAsDeferredUnhandledCompletionExceptionTest : TestBase() {

    // This is a separate test in order to avoid interference with uncaught exception handlers in other tests
    private val exceptionHandler = Thread.getDefaultUncaughtExceptionHandler()
    private lateinit var caughtException: Throwable

    @Before
    fun setUp() {
        Thread.setDefaultUncaughtExceptionHandler { _, e -> caughtException = e }
    }

    @After
    fun tearDown() {
        Thread.setDefaultUncaughtExceptionHandler(exceptionHandler)
    }

    @Test
    fun testLostExceptionOnSuccess() = runTest {
        val future = SettableFuture.create<Int>()
        val deferred = future.asDeferred()
        deferred.invokeOnCompletion { throw TestException() }
        future.set(1)
        assertTrue { caughtException is CompletionHandlerException && caughtException.cause is TestException }
    }

    @Test
    fun testLostExceptionOnFailure() = runTest {
        val future = SettableFuture.create<Int>()
        val deferred = future.asDeferred()
        deferred.invokeOnCompletion { throw TestException() }
        future.setException(TestException2())
        assertTrue { caughtException is CompletionHandlerException && caughtException.cause is TestException }
    }
}
