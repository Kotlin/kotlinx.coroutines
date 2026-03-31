package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext

/**
 * @suppress this is a function that should help users who are trying to use 'launch'
 * without the corresponding coroutine scope. It is not supposed to be called.
 */
@Deprecated("'launch' can not be called without the corresponding coroutine scope. " +
    "Consider wrapping 'launch' in 'coroutineScope { }', using 'runBlocking { }', " +
    "or using some other 'CoroutineScope'", level = DeprecationLevel.ERROR)
@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
@kotlin.internal.LowPriorityInOverloadResolution
public fun launch(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> Unit
): Job {
    throw UnsupportedOperationException("Should never be called, was introduced to help with incomplete code")
}

/**
 * Deprecated version of [launch] that accepts a [Job].
 *
 * See the documentation for the non-deprecated [launch] function to learn about the functionality of this function.
 * This piece of documentation explains why this overload is deprecated.
 *
 * It is incorrect to pass a [Job] as [context] to [launch] or [async], because this violates structured concurrency.
 * The passed [Job] becomes the sole parent of the newly created coroutine, which completely severs the tie between
 * the new coroutine and the [CoroutineScope] in which it is launched.
 *
 * ## Benefits of structured concurrency
 *
 * Structured concurrency ensures that
 * - Cancellation of the parent job cancels the children as well,
 *   which helps avoid unnecessary computations when they are no longer needed.
 * - Cancellation of children also can be necessary for reliability:
 *   if the [CoroutineScope]'s lifecycle is bound to some component that may not be used after it's destroyed,
 *   performing computations after the parent [CoroutineScope] is cancelled may lead to crashes.
 * - For concurrent decomposition of work (when the [CoroutineScope] contains a non-[supervisor][SupervisorJob] job),
 *   failure of the newly created coroutine also causes the sibling coroutines to fail,
 *   improving the responsiveness of the program:
 *   unnecessary computations will not proceed when it's obvious that they are not needed.
 * - The [CoroutineScope] can only complete when all its children complete.
 *   If the [CoroutineScope] is lexically scoped (for example, created by [coroutineScope], [supervisorScope],
 *   or [withContext]), this means that
 *   the lexical scope will only be exited (and the calling function will finish) once all child coroutines complete.
 *
 * ## Possible alternatives
 *
 * In some scenarios, one or more of the properties guaranteed by structured concurrency are actually undesirable.
 * However, breaking structured concurrency altogether and losing the other properties can often be avoided.
 *
 * ### Ignoring cancellation
 *
 * Sometimes, it is undesirable for the child coroutine to react to the cancellation of the parent: for example,
 * some computations have to be performed unconditionally.
 *
 * Seeing `launch(NonCancellable)` in code is a reliable sign that this was the intention.
 * Alternatively, you may see `launch(Job())`.
 * Both patterns break structured concurrency and prevent cancellation from being propagated.
 *
 * Here's an alternative approach that preserves structured concurrency:
 *
 * ```
 * scope.launch(start = CoroutineStart.ATOMIC) {
 *     withContext(NonCancellable) {
 *         // this line will be reached even if the parent is cancelled
 *     }
 * }
 * ```
 *
 * This way, the child coroutine is guaranteed to complete,
 * but the scope is still aware of the child.
 * This allows the parent scope to await the completion of the child and to react to its failure.
 *
 * ### Not cancelling other coroutines on failure
 *
 * Often, the failure of one child does not require the work of the other coroutines to be cancelled.
 *
 * `launch(SupervisorJob())` is a telling sign that this was the reason for breaking structured concurrency in code,
 * though `launch(Job())` has the exact same effect.
 * By breaking structured concurrency, `launch(SupervisorJob()) { error("failure") }` will prevent `failure` from
 * affecting the parent coroutine and the siblings.
 *
 * Occasionally, the failure of one child does not mean the work of the other children is also unneeded.
 * `launch(Job()) { failure() }` makes sure that the only effect of `failure()` is to make *this* `launch` finish
 * with an error, while the other coroutines continue executing.
 *
 * If *all* coroutines in a scope should fail independently, this suggests that the scope
 * is a [*supervisor*][supervisorScope]:
 *
 * ```
 * withContext(CoroutineExceptionHandler { _, e ->
 *     println("Failure($e)")
 * }) {
 *     supervisorScope {
 *         val coroutines = List(10) {
 *             launch {
 *                 delay(10.milliseconds * it)
 *                 throw IllegalStateException("$it is tired of all this")
 *             }
 *         }
 *         coroutines.joinAll() // errors in `launch` don't affect this call!
 *     }
 * }
 * ```
 *
 * Every coroutine here will run to completion and will fail with its own error.
 *
 * For non-lexically-scoped [CoroutineScope] instances,
 * use [SupervisorJob] instead of [Job] when constructing the [CoroutineScope].
 *
 * If only *some* coroutines need to individually have their failures invisible to others
 * in a non-lexically-scoped [CoroutineScope],
 * the correct approach from the point of view of structured concurrency is this:
 *
 * ```
 * val supervisorJob = SupervisorJob(scope.coroutineContext.job)
 * val childSupervisorScope = CoroutineScope(
 *     scope.coroutineContext +
 *     supervisorJob +
 *     CoroutineExceptionHandler { _, e ->
 *         // process errors
 *     }
 * )
 * childSupervisorScope.launch {
 *     // failures in this coroutine will not affect other children
 * }
 * // `cancel` or `complete` the `supervisorJob` when it's no longer needed
 * supervisorJob.complete()
 * supervisorJob.join()
 * ```
 *
 * For a lexically scoped [CoroutineScope], it may be possible to use a [supervisorScope] at the end of the outer scope,
 * depending on the code structure:
 *
 * ```
 * coroutineScope {
 *     val deferred = async {
 *         // failures in this coroutine will affect everyone
 *     }
 *     supervisorScope {
 *         val job = launch(
 *             CoroutineExceptionHandler { _, e ->
 *                 // some individual mechanism of processing exceptions
 *             }
 *         ) {
 *             // failures in this coroutine
 *             // are only available through `job`
 *         }
 *     }
 *     // this line will only be reached when `launch` completes
 * }
 * // this line will be reached when both `async` and `launch` complete
 * ```
 *
 * All of these approaches preserve the ability of a parent to cancel the children and to wait for their completion.
 *
 * ### Avoiding both cancelling and being cancelled
 *
 * Sometimes, coroutines to be spawned are just completely unrelated to the [CoroutineScope] used as the receiver,
 * and no structured concurrency mechanisms are needed.
 *
 * In that case, [GlobalScope] is the semantically clearer way of expressing opting out of structured concurrency:
 *
 * ```
 * GlobalScope.launch(CoroutineExceptionHandler { _, e ->
 *     /* what to do if this coroutine fails */
 * }) {
 *     // this computation is explicitly outside structured concurrency
 * }
 * ```
 *
 * The reason why [GlobalScope] is marked as [delicate][DelicateCoroutinesApi] is exactly that the coroutines
 * created in it are not benefitting from structured concurrency.
 */
@Deprecated(
    "Passing a Job to coroutine builders breaks structured concurrency, leading to hard-to-diagnose errors. " +
        "This pattern should be avoided. " +
        "This overload will be deprecated with an error in the future.",
    level = DeprecationLevel.WARNING)
public fun CoroutineScope.launch(
    context: Job,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> Unit
): Job = launch(context as CoroutineContext, start, block)

/**
 * Deprecated version of [launch] that accepts a [NonCancellable].
 *
 * See the documentation for the non-deprecated [launch] function to learn about the functionality of this function.
 * This piece of documentation explains why this overload is deprecated.
 *
 * Passing [NonCancellable] to [launch] or [async] breaks structured concurrency, completely severing the tie between
 * the new coroutine and the [CoroutineScope] in which it is launched.
 * This has the effect of preventing the new coroutine from being cancelled when the parent coroutine is cancelled,
 * which is probably what was intended.
 * However, in addition to that, it breaks the other aspects of structured concurrency.
 *
 * 1. A [CoroutineScope] only completes when all its children complete.
 *    When [NonCancellable] removes the parent-child tie, the [CoroutineScope] will not wait for the completion of the
 *    new coroutine.
 *    ```
 *    coroutineScope {
 *        launch(NonCancellable) {
 *            delay(100.milliseconds)
 *            println("The child only completes now")
 *        }
 *    }
 *    println("The parent completed before the child")
 *    ```
 * 2. A child typically notifies the parent about its failure by cancelling it.
 *    When [NonCancellable] removes the parent-child tie, the child will not be able to notify the parent about its
 *    failure.
 *    If this is the intended effect, please use [SupervisorJob] or [supervisorScope] to ensure independent failure
 *    of children.
 *    ```
 *    // `launch` will not cancel the `coroutineScope`.
 *    // Instead, without a propagation path, the exception will be passed
 *    // to `CoroutineExceptionHandler` and potentially crash the program.
 *    coroutineScope {
 *        launch(NonCancellable) {
 *            error("The child failed")
 *        }
 *    }
 *    ```
 *
 * A pattern that prevents child cancellation even when the parent is cancelled consists of two parts:
 * - [CoroutineStart.ATOMIC] or [CoroutineStart.UNDISPATCHED] both ensure that the new coroutine is at least going
 *   to be started and run until the first suspension, even if the parent is already cancelled.
 * - Using [NonCancellable] together with [withContext] in the coroutine's body ensures that the child will
 *   successfully resume from suspension points even if the coroutine is cancelled.
 *
 * Example:
 * ```
 * launch(start = CoroutineStart.ATOMIC) {
 *     withContext(NonCancellable) {
 *         // Actual coroutine body here
 *     }
 * }
 * ```
 */
@Deprecated(
    "Passing a NonCancellable to `launch` breaks structured concurrency, leading to hard-to-diagnose errors. " +
        "This pattern should be avoided. " +
        "This overload will be deprecated with an error in the future.",
    level = DeprecationLevel.WARNING,
)
public fun CoroutineScope.launch(
    context: NonCancellable,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> Unit
): Job = launch(context as CoroutineContext, start, block)

/**
 * @suppress this is a function that should help users who are trying to use 'launch'
 * without the corresponding coroutine scope. It is not supposed to be called.
 */
@Deprecated("'async' can not be called without the corresponding coroutine scope. " +
    "Consider wrapping 'async' in 'coroutineScope { }', using 'runBlocking { }', " +
    "or using some other 'CoroutineScope'", level = DeprecationLevel.ERROR)
@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
@kotlin.internal.LowPriorityInOverloadResolution
public fun <T> async(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): Deferred<T> {
    throw UnsupportedOperationException("Should never be called, was introduced to help with incomplete code")
}

/**
 * Deprecated version of [async] that accepts a [Job].
 *
 * See the documentation for the non-deprecated [async] function to learn about the functionality of this function.
 * This piece of documentation explains why this overload is deprecated.
 *
 * It is incorrect to pass a [Job] as [context] to [async] or [launch], because this violates structured concurrency.
 * The passed [Job] becomes the sole parent of the newly created coroutine, which completely severs the tie between
 * the new coroutine and the [CoroutineScope] in which it is launched.
 *
 * ## Benefits of structured concurrency
 *
 * Structured concurrency ensures that
 * - Cancellation of the parent job cancels the children as well,
 *   which helps avoid unnecessary computations when they are no longer needed.
 * - Cancellation of children also can be necessary for reliability:
 *   if the [CoroutineScope]'s lifecycle is bound to some component that may not be used after it's destroyed,
 *   performing computations after the parent [CoroutineScope] is cancelled may lead to crashes.
 * - For concurrent decomposition of work (when the [CoroutineScope] contains a non-[supervisor][SupervisorJob] job),
 *   failure of the newly created coroutine also causes the sibling coroutines to fail,
 *   improving the responsiveness of the program:
 *   unnecessary computations will not proceed when it's obvious that they are not needed.
 * - The [CoroutineScope] can only complete when all its children complete.
 *   If the [CoroutineScope] is lexically scoped (for example, created by [coroutineScope], [supervisorScope],
 *   or [withContext]), this means that
 *   the lexical scope will only be exited (and the calling function will finish) once all child coroutines complete.
 *
 * ## Possible alternatives
 *
 * In some scenarios, one or more of the properties guaranteed by structured concurrency are actually undesirable.
 * However, breaking structured concurrency altogether and losing the other properties can often be avoided.
 *
 * ### Ignoring cancellation
 *
 * Sometimes, it is undesirable for the child coroutine to react to the cancellation of the parent: for example,
 * some computations have to be performed unconditionally.
 *
 * Seeing `async(NonCancellable)` in code is a reliable sign that this was the intention.
 * Alternatively, you may see `async(Job())`.
 * Both patterns break structured concurrency and prevent cancellation from being propagated.
 *
 * Here's an alternative approach that preserves structured concurrency:
 *
 * ```
 * // Guarantees the completion, but not the delivery of the value
 * scope.async(start = CoroutineStart.ATOMIC) {
 *     withContext(NonCancellable) {
 *         // The actual body of the coroutine.
 *         // This code will get executed even if the parent is cancelled.
 *     }
 *     // Note: the cancellation exception *can* be thrown here,
 *     // losing the computed value!
 * }
 *
 * // Guarantees the delivery of the value, but is more complex
 * val asyncResult = CompletableDeferred<T>()
 * scope.launch(start = CoroutineStart.ATOMIC) {
 *     withContext(NonCancellable) {
 *         asyncResult.completeWith(
 *             runCatching {
 *                 // compute the value
 *             }
 *         )
 *     }
 * }
 * ```
 *
 * This way, the child coroutine is guaranteed to complete,
 * but the scope is still aware of the child.
 * This allows the parent scope to await the completion of the child and to react to its failure.
 *
 * ### Not cancelling other coroutines on failure
 *
 * Often, the failure of one child does not require the work of the other coroutines to be cancelled.
 *
 * `async(SupervisorJob())` is a telling sign that this was the reason for breaking structured concurrency in code,
 * though `async(Job())` has the exact same effect.
 * By breaking structured concurrency, `async(SupervisorJob()) { error("failure") }` will prevent `failure` from
 * affecting the parent coroutine and the siblings.
 *
 * If *all* coroutines in a scope should fail independently, this suggests that the scope
 * is a [*supervisor*][supervisorScope]:
 *
 * ```
 * supervisorScope {
 *     val coroutines = List(10) {
 *         async {
 *             delay(10.milliseconds * it)
 *             throw IllegalStateException("$it is tired of all this")
 *         }
 *     }
 *     coroutines.forEach {
 *         println(runCatching { it.await() })
 *     }
 * }
 * ```
 *
 * Every coroutine here will run to completion and will fail with its own error.
 *
 * For non-lexically-scoped [CoroutineScope] instances,
 * use [SupervisorJob] instead of [Job] when constructing the [CoroutineScope].
 *
 * If only *some* coroutines need to individually have their failures invisible to others
 * in a non-lexically-scoped [CoroutineScope],
 * the correct approach from the point of view of structured concurrency is this:
 *
 * ```
 * val supervisorJob = SupervisorJob(scope.coroutineContext.job)
 * val childSupervisorScope = CoroutineScope(
 *     scope.coroutineContext + supervisorJob
 * )
 * childSupervisorScope.async {
 *     // failures in this coroutine will not affect other children
 * }
 * // `cancel` or `complete` the `supervisorJob` when it's no longer needed
 * supervisorJob.complete()
 * supervisorJob.join()
 * ```
 *
 * For a lexically scoped [CoroutineScope], it may be possible to use a [supervisorScope] at the end of the outer scope,
 * depending on the code structure:
 *
 * ```
 * coroutineScope {
 *     launch {
 *         // failures in this coroutine will affect everyone
 *     }
 *     supervisorScope {
 *         val deferred = async {
 *             // failures in this coroutine
 *             // are only available through `deferred`
 *         }
 *     }
 *     // this line will only be reached when `async` completes
 * }
 * // this line will be reached when both `launch` and `async` complete
 * ```
 *
 * All of these approaches preserve the ability of a parent to cancel the children and to wait for their completion.
 *
 * ### Avoiding both cancelling and being cancelled
 *
 * Sometimes, coroutines to be spawned are just completely unrelated to the [CoroutineScope] used as the receiver,
 * and no structured concurrency mechanisms are needed.
 *
 * In that case, [GlobalScope] is the semantically clearer way of expressing opting out of structured concurrency:
 *
 * ```
 * GlobalScope.async {
 *     // this computation is explicitly outside structured concurrency
 * }
 * ```
 *
 * The reason why [GlobalScope] is marked as [delicate][DelicateCoroutinesApi] is exactly that the coroutines
 * created in it are not benefitting from structured concurrency.
 */
@Deprecated(
    "Passing a Job to coroutine builders breaks structured concurrency, leading to hard-to-diagnose errors. " +
        "This pattern should be avoided. " +
        "This overload will be deprecated with an error in the future.",
    level = DeprecationLevel.WARNING)
public fun <T> CoroutineScope.async(
    context: Job,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): Deferred<T> = async(context as CoroutineContext, start, block)

/**
 * Deprecated version of [async] that accepts a [NonCancellable].
 *
 * See the documentation for the non-deprecated [async] function to learn about the functionality of this function.
 * This piece of documentation explains why this overload is deprecated.
 *
 * Passing [NonCancellable] to [launch] or [async] breaks structured concurrency, completely severing the tie between
 * the new coroutine and the [CoroutineScope] in which it is launched.
 * This has the effect of preventing the new coroutine from being cancelled when the parent coroutine is cancelled,
 * which is probably what was intended.
 * However, in addition to that, it breaks the other aspects of structured concurrency.
 *
 * 1. A [CoroutineScope] only completes when all its children complete.
 *    When [NonCancellable] removes the parent-child tie, the [CoroutineScope] will not wait for the completion of the
 *    new coroutine.
 *    ```
 *    coroutineScope {
 *        async(NonCancellable) {
 *            delay(100.milliseconds)
 *            println("The child only completes now")
 *        }
 *    }
 *    println("The parent completed before the child")
 *    ```
 * 2. A child typically notifies the parent about its failure by cancelling it.
 *    When [NonCancellable] removes the parent-child tie, the child will not be able to notify the parent about its
 *    failure.
 *    If this is the intended effect, please use [SupervisorJob] or [supervisorScope] to ensure independent failure
 *    of children.
 *    ```
 *    // `async` will not cancel the `coroutineScope`.
 *    // Instead, the exception will only be available in the resulting `Deferred`.
 *    coroutineScope {
 *        async<Int>(NonCancellable) {
 *            error("The child failed")
 *        }
 *    }
 *    ```
 *
 * A pattern that prevents child cancellation even when the parent is cancelled consists of two parts:
 * - [CoroutineStart.ATOMIC] or [CoroutineStart.UNDISPATCHED] both ensure that the new coroutine is at least going
 *   to be started and run until the first suspension, even if the parent is already cancelled.
 * - Using [NonCancellable] together with [withContext] in the coroutine's body ensures that the child will
 *   successfully resume from suspension points even if the coroutine is cancelled.
 *
 * Example:
 * ```
 * async(start = CoroutineStart.ATOMIC) {
 *     withContext(NonCancellable) {
 *         // Actual coroutine body here
 *     }
 * }
 * ```
 */
@Deprecated(
    "Passing a NonCancellable to `async` breaks structured concurrency, leading to hard-to-diagnose errors. " +
        "This pattern should be avoided. " +
        "This overload will be deprecated with an error in the future.",
    level = DeprecationLevel.WARNING,
)
public fun <T> CoroutineScope.async(
    context: NonCancellable,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): Deferred<T> = async(context as CoroutineContext, start, block)
