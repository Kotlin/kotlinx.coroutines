package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * Helper function for coroutine builder implementations to handle uncaught and unexpected exceptions in coroutines,
 * that could not be otherwise handled in a normal way through structured concurrency, saving them to a future, and
 * cannot be rethrown. This is a last resort handler to prevent lost exceptions.
 *
 * If there is [CoroutineExceptionHandler] in the context, then it is used. If it throws an exception during handling
 * or is absent, all instances of [CoroutineExceptionHandler] found via [ServiceLoader] and
 * [Thread.uncaughtExceptionHandler] are invoked.
 *
 * @suppress **This is internal API and it is subject to change.**
 */
@InternalCoroutinesApi
public fun handleCoroutineException(context: CoroutineContext, exception: Throwable) {
    val reportException = if (exception is DispatchException) exception.cause else exception
    // Invoke an exception handler from the context if present
    try {
        context[CoroutineExceptionHandler]?.let {
            it.handleException(context, reportException)
            return
        }
    } catch (t: Throwable) {
        handleUncaughtCoroutineException(context, handlerException(reportException, t))
        return
    }
    // If a handler is not present in the context or an exception was thrown, fallback to the global handler
    handleUncaughtCoroutineException(context, reportException)
}

internal fun handlerException(originalException: Throwable, thrownException: Throwable): Throwable {
    if (originalException === thrownException) return originalException
    return RuntimeException("Exception while trying to handle coroutine exception", thrownException).apply {
        addSuppressed(originalException)
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
 * If you need to handle the exception in a specific part of the code, it is recommended to use `try`/`catch` around
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
 * ### Uncaught exceptions with no handler
 *
 * When no handler is installed, an exception is handled in the following way:
 * - If the exception is [CancellationException], it is ignored, as these exceptions are used to cancel coroutines.
 * - Otherwise, if there is a [Job] in the context, then [Job.cancel] is invoked.
 * - Otherwise, as a last resort, the exception is processed in a platform-specific manner:
 *   - On JVM, all instances of [CoroutineExceptionHandler] found via [ServiceLoader], as well as
 *     the current thread's [Thread.uncaughtExceptionHandler], are invoked.
 *   - On Native, the whole application crashes with the exception.
 *   - On JS and Wasm JS, the exception is propagated into the JavaScript runtime's event loop
 *     and is processed in a platform-specific way determined by the platform itself.
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
     * if the coroutine has an uncaught exception.
     */
    public fun handleException(context: CoroutineContext, exception: Throwable)
}
