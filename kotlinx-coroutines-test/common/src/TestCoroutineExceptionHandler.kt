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
@Deprecated(
    "Consider whether the default mechanism of handling uncaught exceptions is sufficient. " +
        "If not, try writing your own `CoroutineExceptionHandler` and " +
        "please report your use case at https://github.com/Kotlin/kotlinx.coroutines/issues.",
    level = DeprecationLevel.WARNING
)
public interface UncaughtExceptionCaptor {
    /**
     * List of uncaught coroutine exceptions.
     *
     * The returned list is a copy of the currently caught exceptions.
     * During [cleanupTestCoroutines] the first element of this list is rethrown if it is not empty.
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
    public fun cleanupTestCoroutines()
}

/**
 * An exception handler that captures uncaught exceptions in tests.
 */
@Deprecated(
    "It's better to define one's own `CoroutineExceptionHandler` if you just need to handle '" +
        "uncaught exceptions without a special `TestCoroutineScope` integration.", level = DeprecationLevel.WARNING
)
public class TestCoroutineExceptionHandler :
    AbstractCoroutineContextElement(CoroutineExceptionHandler), CoroutineExceptionHandler, UncaughtExceptionCaptor {
    private val _exceptions = mutableListOf<Throwable>()
    private val _lock = SynchronizedObject()
    private var _coroutinesCleanedUp = false

    @Suppress("INVISIBLE_MEMBER")
    override fun handleException(context: CoroutineContext, exception: Throwable) {
        synchronized(_lock) {
            if (_coroutinesCleanedUp) {
                handleCoroutineExceptionImpl(context, exception)
                return
            }
            _exceptions += exception
        }
    }

    public override val uncaughtExceptions: List<Throwable>
        get() = synchronized(_lock) { _exceptions.toList() }

    public override fun cleanupTestCoroutines() {
        synchronized(_lock) {
            _coroutinesCleanedUp = true
            val exception = _exceptions.firstOrNull() ?: return
            // log the rest
            _exceptions.drop(1).forEach { it.printStackTrace() }
            throw exception
        }
    }
}
