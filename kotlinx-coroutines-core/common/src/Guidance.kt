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
 * ### Avoiding cancellation
 *
 * Sometimes, it is undesirable for the child coroutine to react to the cancellation of the parent: for example,
 * some computations have to be performed either way.
 * `async(NonCancellable)` or `async(Job())` can be used to achieve this effect.
 *
 * An alternative approach that preserves structured concurrency is this:
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
 * but the scope is still aware of the child and can track its lifecycle.
 *
 * ### Avoid cancelling other children
 *
 * Occasionally, the failure of one child does not mean the work of the other children is also unneeded.
 * `launch(Job()) { failure() }` makes sure that the only effect of `failure()` is to make *this* `async` finish
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
 *         coroutines.joinAll()
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
 * val childSupervisorScope = CoroutineScope(
 *     scope.coroutineContext +
 *     SupervisorJob(scope.coroutineContext.job) +
 *     CoroutineExceptionHandler { _, e ->
 *         // process errors
 *     }
 * )
 * childSupervisorScope.launch {
 *     // failures in this coroutine will not affect other children
 * }
 * ```
 *
 * For a lexically scoped [CoroutineScope], using a [supervisorScope] at the end of the outer scope may help:
 *
 * ```
 * coroutineScope {
 *     val deferred = async {
 *         // failures in this coroutine will affect everyone
 *     }
 *     supervisorScope {
 *         val deferred = launch(
 *             CoroutineExceptionHandler { _, e ->
 *                 // some individual mechanism of processing exceptions
 *             }
 *         ) {
 *             // failures in this coroutine
 *             // are only available through `deferred`
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
 *     // this is explicitly a rogue computation
 * }
 * ```
 *
 * The reason why [GlobalScope] is marked as [delicate][DelicateCoroutinesApi] is exactly that the coroutines
 * created in it are outside structured concurrency.
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
 * ### Avoiding cancellation
 *
 * Sometimes, it is undesirable for the child coroutine to react to the cancellation of the parent: for example,
 * some computations have to be performed either way.
 * `async(NonCancellable)` or `async(Job())` can be used to achieve this effect.
 *
 * Alternative approaches that preserve structured concurrency are this:
 *
 * ```
 * // Guarantees the completion, but not the delivery of the value
 * scope.async(start = CoroutineStart.ATOMIC) {
 *     withContext(NonCancellable) {
 *         // this line will be reached even if the parent is cancelled
 *     }
 *     // note: the cancellation exception *can* be thrown here,
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
 * but the scope is still aware of the child and can track its lifecycle.
 *
 * ### Avoid cancelling other children
 *
 * Occasionally, the failure of one child does not mean the work of the other children is also unneeded.
 * `async(Job()) { failure() }` makes sure that the only effect of `failure()` is to make *this* `async` finish
 * with an error, while the other coroutines continue executing.
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
 * val childSupervisorScope = CoroutineScope(
 *     scope.coroutineContext + SupervisorJob(scope.coroutineContext.job)
 * )
 * childSupervisorScope.async {
 *     // failures in this coroutine will not affect other children
 * }
 * ```
 *
 * For a lexically scoped [CoroutineScope], using a [supervisorScope] at the end of the outer scope may help:
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
 *     // this is explicitly a rogue computation
 * }
 * ```
 *
 * The reason why [GlobalScope] is marked as [delicate][DelicateCoroutinesApi] is exactly that the coroutines
 * created in it are outside structured concurrency.
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
