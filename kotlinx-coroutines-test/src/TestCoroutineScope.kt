
/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.CoroutineContext


/**
 * A scope which provides detailed control over the execution of coroutines for tests.
 */
@ExperimentalCoroutinesApi
interface TestCoroutineScope: CoroutineScope, UncaughtExceptionCaptor, DelayController

private class TestCoroutineScopeImpl (
        context: CoroutineContext = TestCoroutineDispatcher() + TestCoroutineExceptionHandler()):
        TestCoroutineScope,
        UncaughtExceptionCaptor by context.uncaughtExceptionDelegate,
        DelayController by context.delayDelegate
{

    override fun cleanupTestCoroutines() {
        coroutineContext.uncaughtExceptionDelegate.cleanupTestCoroutines()
        coroutineContext.delayDelegate.cleanupTestCoroutines()
    }

    override val coroutineContext = context
}

/**
 * A scope which provides detailed control over the execution of coroutines for tests.
 *
 * If the provided context does not provide a [ContinuationInterceptor] (Dispatcher) or [CoroutineExceptionHandler], the
 * scope will add [TestCoroutineDispatcher] and [TestCoroutineExceptionHandler] automatically.
 *
 * @param context an optional context that MAY provide [UncaughtExceptionCaptor] and/or [DelayController]
 */
@ExperimentalCoroutinesApi
fun TestCoroutineScope(context: CoroutineContext? = null): TestCoroutineScope {
    var safeContext = context ?: return TestCoroutineScopeImpl()
    if (context[ContinuationInterceptor] == null) {
        safeContext += TestCoroutineDispatcher()
    }
    if (context[CoroutineExceptionHandler] == null) {
        safeContext += TestCoroutineExceptionHandler()
    }

    return TestCoroutineScopeImpl(safeContext)
}

private inline val CoroutineContext.uncaughtExceptionDelegate: UncaughtExceptionCaptor
    get() {
        val handler = this[CoroutineExceptionHandler]
        return handler as? UncaughtExceptionCaptor ?: throw
            IllegalArgumentException("TestCoroutineScope requires a UncaughtExceptionCaptor such as " +
                    "TestCoroutineExceptionHandler as the CoroutineExceptionHandler")
    }

private inline val CoroutineContext.delayDelegate: DelayController
    get() {
        val handler = this[ContinuationInterceptor]
        return handler as? DelayController ?: throw
            IllegalArgumentException("TestCoroutineScope requires a DelayController such as TestCoroutineDispatcher as " +
                    "the ContinuationInterceptor (Dispatcher)")
    }