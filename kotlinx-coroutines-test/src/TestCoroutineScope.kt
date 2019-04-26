/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * A scope which provides detailed control over the execution of coroutines for tests.
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public interface TestCoroutineScope: CoroutineScope, UncaughtExceptionCaptor, DelayController {
    /**
     * Call after the test completes.
     * Calls [UncaughtExceptionCaptor.cleanupTestCoroutines] and [DelayController.cleanupTestCoroutines].
     *
     * @throws Throwable the first uncaught exception, if there are any uncaught exceptions.
     * @throws UncompletedCoroutinesError if any pending tasks are active, however it will not throw for suspended
     * coroutines.
     */
    public override fun cleanupTestCoroutines()
}

private class TestCoroutineScopeImpl (
    override val coroutineContext: CoroutineContext
):
    TestCoroutineScope,
    UncaughtExceptionCaptor by coroutineContext.uncaughtExceptionCaptor,
    DelayController by coroutineContext.delayController
{
    override fun cleanupTestCoroutines() {
        coroutineContext.uncaughtExceptionCaptor.cleanupTestCoroutines()
        coroutineContext.delayController.cleanupTestCoroutines()
    }
}

/**
 * A scope which provides detailed control over the execution of coroutines for tests.
 *
 * If the provided context does not provide a [ContinuationInterceptor] (Dispatcher) or [CoroutineExceptionHandler], the
 * scope adds [TestCoroutineDispatcher] and [TestCoroutineExceptionHandler] automatically.
 *
 * @param context an optional context that MAY provide [UncaughtExceptionCaptor] and/or [DelayController]
 */
@Suppress("FunctionName")
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public fun TestCoroutineScope(context: CoroutineContext = EmptyCoroutineContext): TestCoroutineScope {
    var safeContext = context
    if (context[ContinuationInterceptor] == null) safeContext += TestCoroutineDispatcher()
    if (context[CoroutineExceptionHandler] == null) safeContext += TestCoroutineExceptionHandler()
    return TestCoroutineScopeImpl(safeContext)
}

private inline val CoroutineContext.uncaughtExceptionCaptor: UncaughtExceptionCaptor
    get() {
        val handler = this[CoroutineExceptionHandler]
        return handler as? UncaughtExceptionCaptor ?: throw IllegalArgumentException(
            "TestCoroutineScope requires a UncaughtExceptionCaptor such as " +
                "TestCoroutineExceptionHandler as the CoroutineExceptionHandler"
        )
    }

private inline val CoroutineContext.delayController: DelayController
    get() {
        val handler = this[ContinuationInterceptor]
        return handler as? DelayController ?: throw IllegalArgumentException(
            "TestCoroutineScope requires a DelayController such as TestCoroutineDispatcher as " +
                "the ContinuationInterceptor (Dispatcher)"
        )
    }