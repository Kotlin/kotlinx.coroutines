@file:OptIn(ExperimentalContracts::class)
@file:Suppress("LEAKED_IN_PLACE_LAMBDA", "WRONG_INVOCATION_KIND")

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.jvm.*

/**
 * Creates a _supervisor_ job object in an active state.
 * Children of a supervisor job can fail independently of each other.
 * 
 * A failure or cancellation of a child does not cause the supervisor job to fail and does not affect its other children,
 * so a supervisor can implement a custom policy for handling failures of its children:
 *
 * - A failure of a child job that was created using [launch][CoroutineScope.launch] can be handled via [CoroutineExceptionHandler] in the context.
 * - A failure of a child job that was created using [async][CoroutineScope.async] can be handled via [Deferred.await] on the resulting deferred value.
 *
 * If a [parent] job is specified, then this supervisor job becomes a child job of the [parent] and is cancelled when the
 * parent fails or is cancelled. All this supervisor's children are cancelled in this case, too.
 */
@Suppress("FunctionName")
public fun SupervisorJob(parent: Job? = null) : CompletableJob = SupervisorJobImpl(parent)

/** @suppress Binary compatibility only */
@Suppress("FunctionName")
@Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
@JvmName("SupervisorJob")
public fun SupervisorJob0(parent: Job? = null) : Job = SupervisorJob(parent)

/**
 * Runs the given [block] in-place in a new [CoroutineScope] with a [SupervisorJob]
 * based on the caller coroutine context, returning its result.
 *
 * The lifecycle of the new [SupervisorJob] begins with starting the [block] and completes when both the [block] and
 * all the coroutines launched in the scope complete.
 *
 * The context of the new scope is obtained by combining the [currentCoroutineContext] with a new [SupervisorJob]
 * whose parent is the [Job] of the caller [currentCoroutineContext] (if any).
 * The [SupervisorJob] of the new scope is not a normal child of the caller coroutine but a lexically scoped one,
 * meaning that the failure of the [SupervisorJob] will not affect the parent [Job].
 * Instead, the exception leading to the failure will be rethrown to the caller of this function.
 *
 * If a child coroutine launched in the new scope fails, it will not affect the other children of the scope.
 * However, if the [block] finishes with an exception, it will cancel the scope and all its children.
 * See [coroutineScope] for a similar function that treats every child coroutine as crucial for obtaining the result
 * and cancels the whole computation if one of them fails.
 *
 * Together, this makes [supervisorScope] a good choice for launching multiple coroutines where some failures
 * are acceptable and should not affect the others.
 *
 * ```
 * // cancelling the caller's coroutine will cancel the new scope and all its children
 * suspend fun tryDownloadFiles(urls: List<String>): List<Deferred<ByteArray>> =
 *     supervisorScope {
 *         urls.map { url ->
 *             async {
 *                 // if one of the downloads fails, the others will continue
 *                 donwloadFileContent(url)
 *             }
 *         }
 *     } // every download will fail or complete by the time this function returns
 * ```
 *
 * Rephrasing this in more practical terms, the specific list of structured concurrency interactions is as follows:
 * - Cancelling the caller's [currentCoroutineContext] leads to cancellation of the new [CoroutineScope]
 *   (corresponding to the code running in the [block]), which in turn cancels all the coroutines launched in it.
 * - If the [block] fails with an exception, the exception is rethrown to the caller,
 *   without directly affecting the caller's [Job].
 * - [supervisorScope] will only finish when all the coroutines launched in it finish.
 *   After that, the [supervisorScope] returns (or rethrows) the result of the [block] to the caller.
 *
 * There is a **prompt cancellation guarantee**: even if this function is ready to return the result, but was cancelled
 * while suspended, [CancellationException] will be thrown. See [suspendCancellableCoroutine] for low-level details.
 *
 * ## Pitfalls
 *
 * ### Uncaught exceptions in child coroutines
 *
 * [supervisorScope] does not install a [CoroutineExceptionHandler] in the new scope.
 * This means that if a child coroutine started with [launch] fails, its exception will be unhandled,
 * possibly crashing the program. Use the following pattern to avoid this:
 *
 * ```
 * withContext(CoroutineExceptionHandler { _, exception ->
 *     // handle the exceptions as needed
 * }) {
 *     supervisorScope {
 *         // launch child coroutines here
 *     }
 * }
 * ```
 *
 * Alternatively, the [CoroutineExceptionHandler] can be supplied to the newly launched coroutines themselves.
 *
 * ### Returning closeable resources
 *
 * Values returned from [supervisorScope] will be lost if the caller is cancelled.
 * See the corresponding section in the [coroutineScope] documentation for details.
 */
public suspend fun <R> supervisorScope(block: suspend CoroutineScope.() -> R): R {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    return suspendCoroutineUninterceptedOrReturn { uCont ->
        val coroutine = SupervisorCoroutine(uCont.context, uCont)
        coroutine.startUndispatchedOrReturn(coroutine, block)
    }
}

private class SupervisorJobImpl(parent: Job?) : JobImpl(parent) {
    override fun childCancelled(cause: Throwable): Boolean = false
}

private class SupervisorCoroutine<in T>(
    context: CoroutineContext,
    uCont: Continuation<T>
) : ScopeCoroutine<T>(context, uCont) {
    override fun childCancelled(cause: Throwable): Boolean = false
}
