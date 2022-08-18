/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.future

import kotlinx.coroutines.*
import kotlinx.coroutines.future.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
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
    fun testLostException() = runTest {
        val future = CompletableFuture<Int>()
        val deferred = future.asDeferred()
        deferred.invokeOnCompletion { throw TestException() }
        future.complete(1)
        assertTrue { caughtException is CompletionHandlerException && caughtException.cause is TestException }
    }
}
