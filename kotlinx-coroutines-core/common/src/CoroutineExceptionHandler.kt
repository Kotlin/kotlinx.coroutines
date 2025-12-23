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
 * An optional element in the [CoroutineContext] to handle coroutine exceptions without a clear propagation path.
 *
 * `kotlinx.coroutines` ensures that every [exception][Throwable] thrown in a coroutine is handled by some code instead
 * of being forgotten about.
 * This helps failures not to go unnoticed, with the program silently entering an incorrect state.
 *
 * In most scenarios, a clear exception propagation path allows processing failures in coroutines: for example,
 * a [coroutineScope] call can rethrow the exception to the caller,
 * and failing coroutines typically [cancel][Job.cancel] their [parent][Job.parent] coroutines.
 * See "Propagation channels recognized by `kotlinx.coroutines`" below for an enumeration of ways an exception in a
 * coroutine can get propagated.
 *
 * However, in some cases, a clear propagation path is not available. Example:
 *
 * ```
 * supervisorScope {
 *     launch { error("Failure") }
 * }
 * ```
 *
 * Here, the coroutine created by `launch` fails with the exception `"Failure"`,
 * and [supervisorScope] does not react to exceptions from its children, as opposed to [coroutineScope].
 *
 * In such cases, a [CoroutineExceptionHandler] should be used to process the exceptions:
 *
 * ```
 * withContext(CoroutineExceptionHandler { ctx, ex ->
 *     println("Exception $ex thrown from coroutine context $ctx")
 * }) {
 *     supervisorScope {
 *         launch { error("Failure") }
 *     }
 * }
 * ```
 *
 * Not handling a lost exception with a [CoroutineExceptionHandler] is treated as a programming error
 * by `kotlinx.coroutines` and will invoke last-resort exception handling, potentially crashing the program.
 * See the "Platform-specific last-resort handling of lost exceptions" section for details.
 *
 * ### Propagation channels recognized by `kotlinx.coroutines`
 *
 * The only exceptions that need to be propagated at all are those with which coroutines finish.
 * If an exception is handled via a `try`/`catch` block inside the coroutine itself,
 * the coroutine machinery will not even learn about it:
 *
 * ```
 * launch {
 *     try {
 *         throw IllegalStateException("""
 *             This is not an unpropagated exception,
 *             since it gets caught.
 *         """)
 *     } catch (_: IllegalStateException) {
 *         println("Caught an exception")
 *     }
 * }
 * ```
 *
 * Exceptions in lexically scoped coroutines are always propagated by being rethrown to the caller:
 *
 * ```
 * // This function will throw an `IllegalStateException`
 * coroutineScope {
 *     throw IllegalStateException("""
 *         This exception is propagated
 *         by being rethrown to the caller.
 *     """)
 * }
 * ```
 *
 * An exception is considered to be propagated if it's transferred to the parent
 * through [structured concurrency][CoroutineScope]:
 *
 * ```
 * coroutineScope {
 *     launch {
 *         throw IllegalStateException("""
 *             This exception is propagated
 *             by `launch` to its parent (`coroutineScope`)
 *             that is able to process child exceptions.
 *         """)
 *     }
 * }
 * ```
 *
 * Finally, an exception is considered to have been propagated
 * if the return value of the coroutine builder allows querying the result of the coroutine's execution:
 *
 * ```
 * val deferred = GlobalScope.async {
 *     throw IllegalStateException("""
 *         This exception is propagated,
 *         since calling `await()` on `deferred`
 *         will rethrow the exception.
 *     """)
 * }
 * ```
 *
 * When none of the propagation channels listed above applies, an exception can not be propagated.
 * Most common examples are coroutines created using the [launch] function on a scope with no [Job] (most notably,
 * [GlobalScope]) or a [SupervisorJob]:
 *
 * ```
 * supervisorScope {
 *     launch {
 *         throw IllegalStateException("""
 *             This *is* an exception with no propagation path, since
 *             1. The block of `launch` finishes with it.
 *             2. `launch` is not lexically scoped,
 *             3. `supervisorScope` does not handle the failures in children,
 *             4. `launch` returns a `Job`, which does not allow querying the exception.
 *         """)
 *     }
 * }
 * ```
 *
 * ```
 * GlobalScope.launch {
 *     throw IllegalStateException("This *is* an unpropagated exception.")
 * }
 * ```
 *
 * ### Platform-specific last-resort handling of lost exceptions
 *
 * When no [CoroutineExceptionHandler] is present in the [CoroutineContext] of the failing coroutine,
 * an exception with no propagation path is handled in the following way as the last-resort measure:
 *
 * - On JVM, all instances of [CoroutineExceptionHandler] found via `ServiceLoader` and
 *   the current thread's [Thread.uncaughtExceptionHandler] are invoked.
 * - On Native, the whole application crashes with the exception.
 * - On JS and Wasm JS, the exception is propagated into the JavaScript runtime's event loop
 *   and is processed in a platform-specific way determined by the platform itself.
 *
 * ### Recommended patterns for handling coroutine exceptions
 *
 * A [CoroutineExceptionHandler] is intended to be a more lenient version of the platform-specific last-resort handling
 * of coroutine exceptions, allowing one to log exceptions, show an error message, restart the program,
 * and in general, fail more gracefully.
 * It is not a replacement for handling exceptions in the normal control flow, and it only gets invoked after the
 * coroutine has completed and can no longer be resumed.
 *
 * If you need to handle the exception in a specific part of the code, it is recommended to use `try`/`catch` around
 * the corresponding code inside your coroutine instead of relying on a [CoroutineExceptionHandler].
 * This way, you can prevent completion of the coroutine with the exception,
 * retry the operation, and/or take arbitrary other actions:
 *
 * ```
 * scope.launch { // launch a child coroutine in a scope
 *     try {
 *          // do something
 *     } catch (e: Throwable) {
 *          // handle exception
 *     }
 * }
 * ```
 *
 * Alternatively, whenever a failure is indeed supposed to terminate a coroutine,
 * using [async] instead of [launch] and later calling [Deferred.await] instead of [Job.join]
 * on its result to check if the computation was successful will allow gracefully processing the exception.
 *
 * ### Pitfalls
 *
 * #### Using a [CoroutineExceptionHandler] does not prevent coroutine failures
 *
 * A [CoroutineExceptionHandler] is only called after the coroutine completes if, informally,
 * the exception has nowhere else to go.
 * A common pitfall is trying to use a [CoroutineExceptionHandler] to prevent the expected failure of a child coroutine
 * from also making the parent coroutine fail:
 *
 * ```
 * coroutineScope {
 *     launch(CoroutineExceptionHandler { ctx, ex ->
 *         println("This line will not be printed!")
 *     }) {
 *         error("This failure will cancel `coroutineScope`!")
 *     }
 * }
 * ```
 *
 * A [CoroutineExceptionHandler] has no effect in this scenario: the failure in [launch] will cancel [coroutineScope].
 * Using `try`/`catch` is the proper way to achieve this.
 *
 * See "Recommended patterns for handling coroutine exceptions" above for more details.
 *
 * #### Overriding [CoroutineExceptionHandler] in coroutines with exception propagation paths has no effect
 *
 * Consider this snippet:
 *
 * ```
 * // Launch the parent coroutine:
 * GlobalScope.launch(CoroutineExceptionHandler { ctx, e -> println("Outer") }) {
 *     // Launch the child coroutine:
 *     launch(CoroutineExceptionHandler { ctx, e -> println("Nested") }) {
 *         error("Error")
 *     }
 * }
 * ```
 *
 * It will print `Outer`, even though the coroutine where the failure originally happened specifies its own
 * [CoroutineExceptionHandler].
 * The explanation is that initially, the exception *does* have a propagation path and will get propagated to the
 * parent coroutine using structured concurrency.
 * The parent itself, however, has no viable propagation channel and has to use *its* [CoroutineExceptionHandler].
 *
 * Similarly, this [CoroutineExceptionHandler] is redundant and will never be invoked:
 *
 * ```
 * GlobalScope.async(CoroutineExceptionHandler { ctx, e -> println("Failure") }) {
 *     error("Error")
 * }
 * ```
 *
 * The caller of [async] is responsible for handling the exceptions in the returned [Deferred] value.
 */
public interface CoroutineExceptionHandler : CoroutineContext.Element {
    /**
     * Key for [CoroutineExceptionHandler] instance in the coroutine context.
     */
    public companion object Key : CoroutineContext.Key<CoroutineExceptionHandler>

    /**
     * Handles uncaught [exception] in the given [context]. It is invoked
     * if the coroutine has an uncaught exception.
     *
     * [handleException] is invoked inside coroutine machinery in an unspecified thread.
     * Therefore, it should be thread-safe and finish quickly.
     *
     * Throwing exceptions from this method is discouraged and
     * will invoke platform-specific last-resort exception handling,
     * described in the [CoroutineExceptionHandler] documentation.
     */
    public fun handleException(context: CoroutineContext, exception: Throwable)
}
