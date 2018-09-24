/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.internal.*
import kotlin.coroutines.experimental.*

internal expect fun handleCoroutineExceptionImpl(context: CoroutineContext, exception: Throwable)

/**
 * Helper function for coroutine builder implementations to handle uncaught exception in coroutines.
 *
 * It tries to handle uncaught exception in the following way:
 * If current exception is [CancellationException], it's ignored: [CancellationException] is a normal way to cancel
 * coroutine.
 *
 * If there is a [Job] in the context and it's not a [caller], then [Job.cancel] is invoked.
 * If invocation returned `true`, method terminates: now [Job] is responsible for handling an exception.
 * Otherwise, If there is [CoroutineExceptionHandler] in the context, it is used. If it throws an exception during handling
 * or is absent, all instances of [CoroutineExceptionHandler] found via [ServiceLoader] and [Thread.uncaughtExceptionHandler] are invoked
 * todo: Deprecate/hide this function.
 */
@JvmOverloads // binary compatibility
public fun handleCoroutineException(context: CoroutineContext, exception: Throwable, caller: Job? = null) {
    // Ignore CancellationException (they are normal ways to terminate a coroutine)
    if (exception is CancellationException) return // nothing to do
    // Try propagate exception to parent
    val job = context[Job]
    if (job !== null && job !== caller && job.cancel(exception)) return // handle by parent
    // otherwise -- use exception handlers
    handleExceptionViaHandler(context, exception)
}

internal fun handleExceptionViaHandler(context: CoroutineContext, exception: Throwable) {
    // Invoke exception handler from the context if present
    try {
        context[CoroutineExceptionHandler]?.let {
            it.handleException(context, exception)
            return
        }
    } catch (t: Throwable) {
        handleCoroutineExceptionImpl(context, handlerException(exception, t))
        return
    }

    // If handler is not present in the context or exception was thrown, fallback to the global handler
    handleCoroutineExceptionImpl(context, exception)
}

internal fun handlerException(originalException: Throwable, thrownException: Throwable): Throwable {
    if (originalException === thrownException) return originalException
    return RuntimeException("Exception while trying to handle coroutine exception", thrownException).apply {
        addSuppressedThrowable(originalException)
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
