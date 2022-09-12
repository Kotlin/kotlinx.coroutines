/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

internal expect fun propagateExceptionToPlatform(context: CoroutineContext, exception: Throwable)

/**
 * If [addOnExceptionCallback] is called, the provided callback will be evaluated each time
 * [handleCoroutineException] is executed and can't find a [CoroutineExceptionHandler] to
 * process the exception.
 *
 * When a callback is registered once, even if it's later removed, the system starts to assume that
 * other callbacks will eventually be registered, and so collects the exceptions.
 * Once a new callback is registered, it tries.
 *
 * The callbacks in this object are the last resort before relying on platform-dependent
 * ways to report uncaught exceptions from coroutines.
 */
@PublishedApi
internal object ExceptionCollector {
    private val lock = SynchronizedObject()
    private var enabled = false
    private var unprocessedExceptions = mutableListOf<Throwable>()
    private val callbacks = mutableMapOf<Any, (Throwable) -> Unit>()

    /**
     * Registers [callback] to be executed when an uncaught exception happens.
     * [owner] is a key by which to distinguish different callbacks.
     */
    fun addOnExceptionCallback(owner: Any, callback: (Throwable) -> Unit) = synchronized(lock) {
        enabled = true // never becomes `false` again
        val previousValue = callbacks.put(owner, callback)
        assert { previousValue === null }
        // try to process the exceptions using the newly-registered callback
        unprocessedExceptions.forEach { reportException(it) }
        unprocessedExceptions = mutableListOf()
    }

    /**
     * Unregisters the callback associated with [owner].
     */
    fun removeOnExceptionCallback(owner: Any) = synchronized(lock) {
        val existingValue = callbacks.remove(owner)
        assert { existingValue !== null }
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
}

internal fun handleUncaughtCoroutineException(context: CoroutineContext, exception: Throwable) {
    // TODO: if ANDROID_DETECTED
    if (!ExceptionCollector.handleException(exception))
        propagateExceptionToPlatform(context, exception)
}

/**
 * Helper function for coroutine builder implementations to handle uncaught and unexpected exceptions in coroutines,
 * that could not be otherwise handled in a normal way through structured concurrency, saving them to a future, and
 * cannot be rethrown. This is a last resort handler to prevent lost exceptions.
 *
 * If there is [CoroutineExceptionHandler] in the context, then it is used. If it throws an exception during handling
 * or is absent, all instances of [CoroutineExceptionHandler] found via [ServiceLoader] and
 * [Thread.uncaughtExceptionHandler] are invoked.
 */
@InternalCoroutinesApi
public fun handleCoroutineException(context: CoroutineContext, exception: Throwable) {
    // Invoke an exception handler from the context if present
    try {
        context[CoroutineExceptionHandler]?.let {
            it.handleException(context, exception)
            return
        }
    } catch (t: Throwable) {
        handleUncaughtCoroutineException(context, handlerException(exception, t))
        return
    }
    // If a handler is not present in the context or an exception was thrown, fallback to the global handler
    handleUncaughtCoroutineException(context, exception)
}

internal fun handlerException(originalException: Throwable, thrownException: Throwable): Throwable {
    if (originalException === thrownException) return originalException
    return RuntimeException("Exception while trying to handle coroutine exception", thrownException).apply {
        addSuppressedThrowable(originalException)
    }
}

/**
 * Creates a [CoroutineExceptionHandler] instance.
 * @param handler a function which handles exception thrown by a coroutine
 */
@Suppress("FunctionName")
public inline fun CoroutineExceptionHandler(crossinline handler: (CoroutineContext, Throwable) -> Unit): CoroutineExceptionHandler =
    object : AbstractCoroutineContextElement(CoroutineExceptionHandler), CoroutineExceptionHandler {
        override fun handleException(context: CoroutineContext, exception: Throwable) =
            handler.invoke(context, exception)
    }

/**
 * An optional element in the coroutine context to handle **uncaught** exceptions.
 *
 * Normally, uncaught exceptions can only result from _root_ coroutines created using the [launch][CoroutineScope.launch] builder.
 * All _children_ coroutines (coroutines created in the context of another [Job]) delegate handling of their
 * exceptions to their parent coroutine, which also delegates to the parent, and so on until the root,
 * so the `CoroutineExceptionHandler` installed in their context is never used.
 * Coroutines running with [SupervisorJob] do not propagate exceptions to their parent and are treated like root coroutines.
 * A coroutine that was created using [async][CoroutineScope.async] always catches all its exceptions and represents them
 * in the resulting [Deferred] object, so it cannot result in uncaught exceptions.
 *
 * ### Handling coroutine exceptions
 *
 * `CoroutineExceptionHandler` is a last-resort mechanism for global "catch all" behavior.
 * You cannot recover from the exception in the `CoroutineExceptionHandler`. The coroutine had already completed
 * with the corresponding exception when the handler is called. Normally, the handler is used to
 * log the exception, show some kind of error message, terminate, and/or restart the application.
 *
 * If you need to handle exception in a specific part of the code, it is recommended to use `try`/`catch` around
 * the corresponding code inside your coroutine. This way you can prevent completion of the coroutine
 * with the exception (exception is now _caught_), retry the operation, and/or take other arbitrary actions:
 *
 * ```
 * scope.launch { // launch child coroutine in a scope
 *     try {
 *          // do something
 *     } catch (e: Throwable) {
 *          // handle exception
 *     }
 * }
 * ```
 *
 * ### Implementation details
 *
 * By default, when no handler is installed, uncaught exception are handled in the following way:
 * * If exception is [CancellationException] then it is ignored
 *   (because that is the supposed mechanism to cancel the running coroutine)
 * * Otherwise:
 *     * if there is a [Job] in the context, then [Job.cancel] is invoked;
 *     * Otherwise, all instances of [CoroutineExceptionHandler] found via [ServiceLoader]
 *     * and current thread's [Thread.uncaughtExceptionHandler] are invoked.
 *
 * [CoroutineExceptionHandler] can be invoked from an arbitrary thread.
 */
public interface CoroutineExceptionHandler : CoroutineContext.Element {
    /**
     * Key for [CoroutineExceptionHandler] instance in the coroutine context.
     */
    public companion object Key : CoroutineContext.Key<CoroutineExceptionHandler>

    /**
     * Handles uncaught [exception] in the given [context]. It is invoked
     * if coroutine has an uncaught exception.
     */
    public fun handleException(context: CoroutineContext, exception: Throwable)
}
