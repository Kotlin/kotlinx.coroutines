/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.CoroutineContext

/**
 * A scope which provides detailed control over the execution of coroutines for tests.
 *
 * @param context an optional context that must provide delegates [ExceptionCaptor] and [DelayController]
 */
class TestCoroutineScope(
        context: CoroutineContext = TestCoroutineDispatcher() + TestCoroutineExceptionHandler()):
        CoroutineScope,
        ExceptionCaptor by context.exceptionDelegate,
        DelayController by context.delayDelegate
{
    override fun cleanupTestCoroutines() {
        coroutineContext.exceptionDelegate.cleanupTestCoroutines()
        coroutineContext.delayDelegate.cleanupTestCoroutines()
    }

    override val coroutineContext = context

    /**
     * This method is deprecated.
     *
     * @see [cleanupTestCoroutines]
     */
    @Deprecated("This API has been deprecated to integrate with Structured Concurrency.",
            ReplaceWith("cleanupTestCoroutines()"),
            level = DeprecationLevel.WARNING)
    fun cancelAllActions() = cleanupTestCoroutines()
}

fun TestCoroutineScope(dispatcher: TestCoroutineDispatcher) =
        TestCoroutineScope(dispatcher + TestCoroutineExceptionHandler())

private inline val CoroutineContext.exceptionDelegate: ExceptionCaptor
    get() {
        val handler = this[CoroutineExceptionHandler]
        return handler as? ExceptionCaptor ?: throw
            IllegalArgumentException("TestCoroutineScope requires a ExceptionCaptor as the " +
                    "CoroutineExceptionHandler")
    }

private inline val CoroutineContext.delayDelegate: DelayController
    get() {
        val handler = this[ContinuationInterceptor]
        return handler as? DelayController ?: throw
            IllegalArgumentException("TestCoroutineScope requires a DelayController as the " +
                    "ContinuationInterceptor (Dispatcher)")
    }