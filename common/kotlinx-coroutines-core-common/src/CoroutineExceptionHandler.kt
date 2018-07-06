/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*

internal expect fun handleCoroutineExceptionImpl(context: CoroutineContext, exception: Throwable)

/**
 * Helper function for coroutine builder implementations to handle uncaught exception in coroutines.
 *
 * It tries to handle uncaught exception in the following way:
 * * If there is [CoroutineExceptionHandler] in the context, then it is used.
 * * Otherwise, if exception is [CancellationException] then it is ignored
 *   (because that is the supposed mechanism to cancel the running coroutine)
 * * Otherwise:
 *     * if there is a [Job] in the context, then [Job.cancel] is invoked;
 *     * all instances of [CoroutineExceptionHandler] found via [ServiceLoader] are invoked;
 *     * current thread's [Thread.uncaughtExceptionHandler] is invoked.
 */
public fun handleCoroutineException(context: CoroutineContext, exception: Throwable) {
    // if exception handling fails, make sure the original exception is not lost
    try {
        context[CoroutineExceptionHandler]?.let {
            it.handleException(context, exception)
            return
        }
        // ignore CancellationException (they are normal means to terminate a coroutine)
        if (exception is CancellationException) return
        // try cancel job in the context
        context[Job]?.cancel(exception)
        // platform-specific
        handleCoroutineExceptionImpl(context, exception)
    } catch (handlerException: Throwable) {
        // simply rethrow if handler threw the original exception
        if (handlerException === exception) throw exception
        // handler itself crashed for some other reason -- that is bad -- keep both
        throw RuntimeException("Exception while trying to handle coroutine exception", exception).apply {
            addSuppressedThrowable(handlerException)
        }
    }
}

/**
 * Creates new [CoroutineExceptionHandler] instance.
 * @param handler a function which handles exception thrown by a coroutine
 */
@Suppress("FunctionName")
public inline fun CoroutineExceptionHandler(crossinline handler: (CoroutineContext, Throwable) -> Unit): CoroutineExceptionHandler =
    object: AbstractCoroutineContextElement(CoroutineExceptionHandler), CoroutineExceptionHandler {
        override fun handleException(context: CoroutineContext, exception: Throwable) =
            handler.invoke(context, exception)
    }

/**
 * An optional element on the coroutine context to handle uncaught exceptions.
 *
 * By default, when no handler is installed, uncaught exception are handled in the following way:
 * * If exception is [CancellationException] then it is ignored
 *   (because that is the supposed mechanism to cancel the running coroutine)
 * * Otherwise:
 *     * if there is a [Job] in the context, then [Job.cancel] is invoked;
 *     * all instances of [CoroutineExceptionHandler] found via [ServiceLoader] are invoked;
 *     * and current thread's [Thread.uncaughtExceptionHandler] is invoked.
 *
 * See [handleCoroutineException].
 */
public interface CoroutineExceptionHandler : CoroutineContext.Element {
    /**
     * Key for [CoroutineExceptionHandler] instance in the coroutine context.
     */
    public companion object Key : CoroutineContext.Key<CoroutineExceptionHandler>

    /**
     * Handles uncaught [exception] in the given [context]. It is invoked
     * if coroutine has an uncaught exception. See [handleCoroutineException].
     */
    public fun handleException(context: CoroutineContext, exception: Throwable)
}
