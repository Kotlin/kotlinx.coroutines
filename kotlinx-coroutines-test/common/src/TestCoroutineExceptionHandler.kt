/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * Access uncaught coroutine exceptions captured during test execution.
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public interface UncaughtExceptionCaptor {
    /**
     * List of uncaught coroutine exceptions.
     *
     * The returned list is a copy of the currently caught exceptions.
     * During [cleanupTestCoroutinesCaptor] the first element of this list is rethrown if it is not empty.
     */
    public val uncaughtExceptions: List<Throwable>

    /**
     * Call after the test completes to ensure that there were no uncaught exceptions.
     *
     * The first exception in uncaughtExceptions is rethrown. All other exceptions are
     * printed using [Throwable.printStackTrace].
     *
     * @throws Throwable the first uncaught exception, if there are any uncaught exceptions.
     */
    public fun cleanupTestCoroutinesCaptor()
}

/**
 * An exception handler that captures uncaught exceptions in tests.
 */
@ExperimentalCoroutinesApi // Since 1.2.1, tentatively till 1.3.0
public class TestCoroutineExceptionHandler :
    AbstractCoroutineContextElement(CoroutineExceptionHandler), UncaughtExceptionCaptor, CoroutineExceptionHandler
{
    private val _exceptions = mutableListOf<Throwable>()
    private val _lock = SynchronizedObject()

    /** @suppress **/
    override fun handleException(context: CoroutineContext, exception: Throwable) {
        synchronized(_lock) {
            _exceptions += exception
        }
    }

    /** @suppress **/
    override val uncaughtExceptions: List<Throwable>
        get() = synchronized(_lock) { _exceptions.toList() }

    /** @suppress **/
    override fun cleanupTestCoroutinesCaptor() {
        synchronized(_lock) {
            val exception = _exceptions.firstOrNull() ?: return
            // log the rest
            _exceptions.drop(1).forEach { it.printStackTrace() }
            throw exception
        }
    }
}
