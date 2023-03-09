/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * If [addOnExceptionCallback] is called, the provided callback will be evaluated each time
 * [handleCoroutineException] is executed and can't find a [CoroutineExceptionHandler] to
 * process the exception.
 *
 * When a callback is registered once, even if it's later removed, the system starts to assume that
 * other callbacks will eventually be registered, and so collects the exceptions.
 * Once a new callback is registered, the collected exceptions are used with it.
 *
 * The callbacks in this object are the last resort before relying on platform-dependent
 * ways to report uncaught exceptions from coroutines.
 */
internal object ExceptionCollector : AbstractCoroutineContextElement(CoroutineExceptionHandler), CoroutineExceptionHandler {
    private val lock = SynchronizedObject()
    private var enabled = false
    private val unprocessedExceptions = mutableListOf<Throwable>()
    private val callbacks = mutableMapOf<Any, (Throwable) -> Unit>()

    /**
     * Registers [callback] to be executed when an uncaught exception happens.
     * [owner] is a key by which to distinguish different callbacks.
     */
    fun addOnExceptionCallback(owner: Any, callback: (Throwable) -> Unit) = synchronized(lock) {
        enabled = true // never becomes `false` again
        val previousValue = callbacks.put(owner, callback)
        check(previousValue === null)
        // try to process the exceptions using the newly-registered callback
        unprocessedExceptions.forEach { reportException(it) }
        unprocessedExceptions.clear()
    }

    /**
     * Unregisters the callback associated with [owner].
     */
    fun removeOnExceptionCallback(owner: Any) = synchronized(lock) {
        val existingValue = callbacks.remove(owner)
        check(existingValue !== null)
    }

    /**
     * Tries to handle the exception by propagating it to an interested consumer.
     * Returns `true` if the exception does not need further processing.
     *
     * Doesn't throw.
     */
    fun handleException(exception: Throwable): Boolean = synchronized(lock) {
        if (!enabled) return false
        if (reportException(exception)) return true
        /** we don't return the result of the `add` function because we don't have a guarantee
         * that a callback will eventually appear and collect the unprocessed exceptions, so
         * we can't consider [exception] to be properly handled. */
        unprocessedExceptions.add(exception)
        return false
    }

    /**
     * Try to report [exception] to the existing callbacks.
     */
    private fun reportException(exception: Throwable): Boolean {
        var executedACallback = false
        for (callback in callbacks.values) {
            callback(exception)
            executedACallback = true
            /** We don't leave the function here because we want to fan-out the exceptions to every interested consumer,
             * it's not enough to have the exception processed by one of them.
             * The reason is, it's less big of a deal to observe multiple concurrent reports of bad behavior than not
             * to observe the report in the exact callback that is connected to that bad behavior. */
        }
        return executedACallback
    }

    @Suppress("INVISIBLE_MEMBER")
    override fun handleException(context: CoroutineContext, exception: Throwable) {
        if (handleException(exception)) {
            throw ExceptionSuccessfullyProcessed
        }
    }

    override fun equals(other: Any?): Boolean = other is ExceptionCollector || other is ExceptionCollectorAsService
}

/**
 * A workaround for being unable to treat an object as a `ServiceLoader` service.
 */
internal class ExceptionCollectorAsService: CoroutineExceptionHandler by ExceptionCollector {
    override fun equals(other: Any?): Boolean = other is ExceptionCollectorAsService || other is ExceptionCollector
    override fun hashCode(): Int = ExceptionCollector.hashCode()
}
