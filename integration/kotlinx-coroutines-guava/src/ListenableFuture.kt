/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.guava

import com.google.common.util.concurrent.*
import com.google.common.util.concurrent.internal.*
import kotlinx.coroutines.*
import java.util.concurrent.*
import java.util.concurrent.CancellationException
import kotlin.coroutines.*

/**
 * Starts [block] in a new coroutine and returns a [ListenableFuture] pointing to its result.
 *
 * The coroutine is immediately started. Passing [CoroutineStart.LAZY] to [start] throws
 * [IllegalArgumentException], because Futures don't have a way to start lazily.
 *
 * The created coroutine is cancelled when the resulting future completes successfully, fails, or
 * is cancelled.
 *
 * `CoroutineContext` is inherited from this [CoroutineScope]. Additional context elements can be
 * added/overlaid by passing [context].
 *
 * If the context does not have a [CoroutineDispatcher], nor any other [ContinuationInterceptor]
 * member, [Dispatchers.Default] is used.
 *
 * The parent job is inherited from this [CoroutineScope], and can be overridden by passing
 * a [Job] in [context].
 *
 * See [newCoroutineContext][CoroutineScope.newCoroutineContext] for a description of debugging
 * facilities.
 *
 * Note that the error and cancellation semantics of [future] are _subtly different_ than
 * [asListenableFuture]'s. See [ListenableFutureCoroutine] for details.
 *
 * @param context added overlaying [CoroutineScope.coroutineContext] to form the new context.
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param block the code to execute.
 */
public fun <T> CoroutineScope.future(
    context: CoroutineContext = EmptyCoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend CoroutineScope.() -> T
): ListenableFuture<T> {
    require(!start.isLazy) { "$start start is not supported" }
    val newContext = newCoroutineContext(context)
    // TODO: It'd be nice not to leak this SettableFuture reference, which is easily blind-cast.
    val future = SettableFuture.create<T>()
    val coroutine = ListenableFutureCoroutine(newContext, future)
    future.addListener(
      coroutine,
      MoreExecutors.directExecutor())
    coroutine.start(start, coroutine, block)
    return future
}

/**
 * Returns a [Deferred] that is completed or failed by `this` [ListenableFuture].
 *
 * Completion is non-atomic between the two promises.
 *
 * Cancellation is propagated bidirectionally.
 *
 * When `this` `ListenableFuture` completes (either successfully or exceptionally) it will try to
 * complete the returned `Deferred` with the same value or exception. This will succeed, barring a
 * race with cancellation of the `Deferred`.
 *
 * When `this` `ListenableFuture` is [successfully cancelled][java.util.concurrent.Future.cancel],
 * it will cancel the returned `Deferred`.
 *
 * When the returned `Deferred` is [cancelled][Deferred.cancel()], it will try to propagate the
 * cancellation to `this` `ListenableFuture`. Propagation will succeed, barring a race with the
 * `ListenableFuture` completing normally. This is the only case in which the returned `Deferred`
 * will complete with a different outcome than `this` `ListenableFuture`.
 */
public fun <T> ListenableFuture<T>.asDeferred(): Deferred<T> {
    /* This method creates very specific behaviour as it entangles the `Deferred` and
     * `ListenableFuture`. This behaviour is the best discovered compromise between the possible
     * states and interface contracts of a `Future` and the states of a `Deferred`. The specific
     * behaviour is described here.
     *
     * When `this` `ListenableFuture` is successfully cancelled - meaning
     * `ListenableFuture.cancel()` returned `true` - it will synchronously cancel the returned
     * `Deferred`. This can only race with cancellation of the returned `Deferred`, so the
     * `Deferred` will always be put into its "cancelling" state and (barring uncooperative
     * cancellation) _eventually_ reach its "cancelled" state when either promise is successfully
     * cancelled.
     *
     * When the returned `Deferred` is cancelled, `ListenableFuture.cancel()` will be synchronously
     * called on `this` `ListenableFuture`. This will attempt to cancel the `Future`, though
     * cancellation may not succeed and the `ListenableFuture` may complete in a non-cancelled
     * terminal state.
     *
     * The returned `Deferred` may receive and suppress the `true` return value from
     * `ListenableFuture.cancel()` when the task is cancelled via the `Deferred` reference to it.
     * This is unavoidable, so make sure no idempotent cancellation work is performed by a
     * reference-holder of the `ListenableFuture` task. The idempotent work won't get done if
     * cancellation was from the `Deferred` representation of the task.
     *
     * This is inherently a race. See `Future.cancel()` for a description of `Future` cancellation
     * semantics. See `Job` for a description of coroutine cancellation semantics.
     */
    // First, try the fast-fast error path for Guava ListenableFutures. This will save allocating an
    // Exception by using the same instance the Future created.
    if (this is InternalFutureFailureAccess) {
        val t: Throwable? = InternalFutures.tryInternalFastPathGetFailure(this)
        if (t != null) {
            return CompletableDeferred<T>().also {
                it.completeExceptionally(t)
            }
        }
    }

    // Second, try the fast path for a completed Future. The Future is known to be done, so get()
    // will not block, and thus it won't be interrupted. Calling getUninterruptibly() instead of
    // getDone() in this known-non-interruptible case saves the volatile read that getDone() uses to
    // handle interruption.
    if (isDone) {
        return try {
            CompletableDeferred(Uninterruptibles.getUninterruptibly(this))
        } catch (e: CancellationException) {
            CompletableDeferred<T>().also { it.cancel(e) }
        } catch (e: ExecutionException) {
            // ExecutionException is the only kind of exception that can be thrown from a gotten
            // Future. Anything else showing up here indicates a very fundamental bug in a
            // Future implementation.
            CompletableDeferred<T>().also { it.completeExceptionally(e.nonNullCause()) }
        }
    }

    // Finally, if this isn't done yet, attach a Listener that will complete the Deferred.
    val deferred = CompletableDeferred<T>()
    Futures.addCallback(this, object : FutureCallback<T> {
        override fun onSuccess(result: T?) {
            // Here we work with flexible types, so we unchecked cast to trick the type system
            @Suppress("UNCHECKED_CAST")
            deferred.complete(result as T)
        }

        override fun onFailure(t: Throwable) {
            deferred.completeExceptionally(t)
        }
    }, MoreExecutors.directExecutor())

    // ... And cancel the Future when the deferred completes. Since the return type of this method
    // is Deferred, the only interaction point from the caller is to cancel the Deferred. If this
    // completion handler runs before the Future is completed, the Deferred must have been
    // cancelled and should propagate its cancellation. If it runs after the Future is completed,
    // this is a no-op.
    deferred.invokeOnCompletion {
        cancel(false)
    }
    return deferred
}

/**
 * Returns the cause from an [ExecutionException] thrown by a [Future.get] or similar.
 *
 * [ExecutionException] _always_ wraps a non-null cause when Future.get() throws. A Future cannot
 * fail without a non-null `cause`, because the only way a Future _can_ fail is an uncaught
 * [Exception].
 *
 * If this !! throws [NullPointerException], a Future is breaking its interface contract and losing
 * state - a serious fundamental bug.
 */
private fun ExecutionException.nonNullCause(): Throwable {
  return this.cause!!
}

/**
 * Returns a [ListenableFuture] that is completed or failed by `this` [Deferred].
 *
 * Completion is non-atomic between the two promises.
 *
 * When either promise successfully completes, it will attempt to synchronously complete its
 * counterpart with the same value. This will succeed barring a race with cancellation.
 *
 * When either promise completes with an Exception, it will attempt to synchronously complete its
 * counterpart with the same Exception. This will succeed barring a race with cancellation.
 *
 * Cancellation is propagated bidirectionally.
 *
 * When the returned [Future] is successfully cancelled - meaning [Future.cancel] returned true -
 * [Deferred.cancel] will be synchronously called on `this` [Deferred]. This will attempt to cancel
 * the `Deferred`, though cancellation may not succeed and the `Deferred` may complete in a
 * non-cancelled terminal state.
 *
 * When `this` `Deferred` reaches its "cancelled" state with a successful cancellation - meaning it
 * completes with [kotlinx.coroutines.CancellationException] - `this` `Deferred` will synchronously
 * cancel the returned `Future`. This can only race with cancellation of the returned `Future`, so
 * the returned `Future` will always _eventually_ reach its cancelled state when either promise is
 * successfully cancelled, for their different meanings of "successfully cancelled".
 *
 * This is inherently a race. See [Future.cancel] for a description of `Future` cancellation
 * semantics. See [Job] for a description of coroutine cancellation semantics. See
 * [DeferredListenableFuture.cancel] for greater detail on the overlapped cancellation semantics and
 * corner cases of this method.
 */
public fun <T> Deferred<T>.asListenableFuture(): ListenableFuture<T> {
    val outerFuture = OuterFuture<T>(this)
    outerFuture.afterInit()
    return outerFuture
}

/**
 * Awaits completion of `this` [ListenableFuture] without blocking a thread.
 *
 * This suspend function is cancellable.
 *
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * stops waiting for the future and immediately resumes with [CancellationException][kotlinx.coroutines.CancellationException].
 *
 * This method is intended to be used with one-shot Futures, so on coroutine cancellation, the Future is cancelled as well.
 * If cancelling the given future is undesired, use [Futures.nonCancellationPropagating] or
 * [kotlinx.coroutines.NonCancellable].
 *
 */
public suspend fun <T> ListenableFuture<T>.await(): T {
    try {
        if (isDone) return Uninterruptibles.getUninterruptibly(this)
    } catch (e: ExecutionException) {
        // ExecutionException is the only kind of exception that can be thrown from a gotten
        // Future, other than CancellationException. Cancellation is propagated upward so that
        // the coroutine running this suspend function may process it.
        // Any other Exception showing up here indicates a very fundamental bug in a
        // Future implementation.
        throw e.nonNullCause()
    }

    return suspendCancellableCoroutine { cont: CancellableContinuation<T> ->
        addListener(
          ToContinuation(this, cont),
          MoreExecutors.directExecutor())
        cont.invokeOnCancellation {
            cancel(false)
        }
    }
}

/**
 * Propagates the outcome of [futureToObserve] to [continuation] on completion.
 *
 * Cancellation is propagated as cancelling the continuation. If [futureToObserve] completes
 * and fails, the cause of the Future will be propagated without a wrapping
 * [ExecutionException] when thrown.
 */
private class ToContinuation<T>(
    val futureToObserve: ListenableFuture<T>,
    val continuation: CancellableContinuation<T>
): Runnable {
    override fun run() {
        if (futureToObserve.isCancelled) {
            continuation.cancel()
        } else {
            try {
                continuation.resumeWith(
                  Result.success(Uninterruptibles.getUninterruptibly(futureToObserve)))
            } catch (e: ExecutionException) {
                // ExecutionException is the only kind of exception that can be thrown from a gotten
                // Future. Anything else showing up here indicates a very fundamental bug in a
                // Future implementation.
                continuation.resumeWithException(e.nonNullCause())
            }
        }
    }
}

/**
 * An [AbstractCoroutine] intended for use directly creating a [ListenableFuture] handle to
 * completion.
 *
 * The code in the [Runnable] portion of the class is registered as a [ListenableFuture] callback.
 * See [run] for details. Both types are implemented by this object to save an allocation.
 */
private class ListenableFutureCoroutine<T>(
    context: CoroutineContext,
    private val future: SettableFuture<T>
) : AbstractCoroutine<T>(context), Runnable  {

    /**
     * When registered as a [ListenableFuture] listener, cancels the returned [Coroutine] if
     * [future] is successfully cancelled. By documented contract, a [Future] has been cancelled if
     * and only if its `isCancelled()` method returns true.
     *
     * Any error that occurs after successfully cancelling a [ListenableFuture]
     * created by submitting the returned object as a [Runnable] to an `Executor` will be passed
     * to the [CoroutineExceptionHandler] from the context. The contract of [Future] does not permit
     * it to return an error after it is successfully cancelled.
     *
     * By calling [asListenableFuture] on a [Deferred], any error that occurs after successfully
     * cancelling the [ListenableFuture] representation of the [Deferred] will _not_ be passed to
     * the [CoroutineExceptionHandler]. Cancelling a [Deferred] places that [Deferred] in the
     * cancelling/cancelled states defined by [Job], which _can_ show the error. It's assumed that
     * the [Deferred] pointing to the task will be used to observe any error outcome occurring after
     * cancellation.
     *
     * This may be counterintuitive, but it maintains the error and cancellation contracts of both
     * the [Deferred] and [ListenableFuture] types, while permitting both kinds of promise to point
     * to the same running task.
     */
    override fun run() {
        if (future.isCancelled) {
            cancel()
        }
    }

    override fun onCompleted(value: T) {
        future.set(value)
    }

    // TODO: This doesn't actually cancel the Future. There doesn't seem to be bidi cancellation?
    override fun onCancelled(cause: Throwable, handled: Boolean) {
        if (!future.setException(cause) && !handled) {
            // prevents loss of exception that was not handled by parent & could not be set to SettableFuture
            handleCoroutineException(context, cause)
        }
    }
}

/**
 * A [ListenableFuture] that delegates to an internal [DeferredListenableFuture], collaborating with
 * it.
 *
 * This setup allows the returned [ListenableFuture] to maintain the following properties:
 *
 * - Correct implementation of [Future]'s happens-after semantics documented for [get], [isDone]
 *   and [isCancelled] methods
 * - Cancellation propagation both to and from [Deferred]
 * - Correct cancellation and completion semantics even when this [ListenableFuture] is combined
 *   with different concrete implementations of [ListenableFuture]
 *   - Fully correct cancellation and listener happens-after obeying [Future] and
 *     [ListenableFuture]'s documented and implicit contracts is surprisingly difficult to achieve.
 *     The best way to be correct, especially given the fun corner cases from
 *     [AsyncFuture.setAsync], is to just use an [AsyncFuture].
 *   - To maintain sanity, this class implements [ListenableFuture] and uses an inner [AsyncFuture]
 *     around its input [deferred] as a state engine to establish happens-after-completion. This
 *     could probably be compressed into one subclass of [AsyncFuture] to save an allocation, at the
 *     cost of the implementation's readability.
 */
private class OuterFuture<T>(private val deferred: Deferred<T>): ListenableFuture<T> {
    val innerFuture = DeferredListenableFuture(deferred)

    // Adding the listener after initialization resolves partial construction hairpin problem.
    //
    // This invokeOnCompletion completes the innerFuture as `deferred`  does. The innerFuture may
    // have completed earlier if it got cancelled! See DeferredListenableFuture.
    fun afterInit() {
        deferred.invokeOnCompletion {
            innerFuture.complete()
        }
    }

    /**
     * Returns cancellation _in the sense of [Future]_. This is _not_ equivalent to
     * [Job.isCancelled].
     *
     * When done, this Future is cancelled if its innerFuture is cancelled, or if its delegate
     * [deferred] is cancelled. Cancellation of [innerFuture] collaborates with this class.
     *
     * See [DeferredListenableFuture.cancel].
     */
    override fun isCancelled(): Boolean {
        // This expression ensures that isCancelled() will *never* return true when isDone() returns false.
        // In the case that the deferred has completed with cancellation, completing `this`, its
        // reaching the "cancelled" state with a cause of CancellationException is treated as the
        // same thing as innerFuture getting cancelled. If the Job is in the "cancelling" state and
        // this Future hasn't itself been successfully cancelled, the Future will return
        // isCancelled() == false. This is the only discovered way to reconcile the two different
        // cancellation contracts.
        return isDone
          && (innerFuture.isCancelled
          || deferred.getCompletionExceptionOrNull() is kotlinx.coroutines.CancellationException)
    }

    /**
     * Waits for [innerFuture] to complete by blocking, then uses the [deferred] returned by that
     * Future to get the `T` value `this` [ListenableFuture] is pointing to. This establishes
     * happens-after ordering for completion of the [Deferred] input to [OuterFuture].
     *
     * `innerFuture` _must be complete_ in order for the [isDone] and [isCancelled] happens-after
     * contract of [Future] to be correctly followed. If this method were to directly use
     * _`this.deferred`_ instead of blocking on its `innerFuture`, the [Deferred] that this
     * [ListenableFuture] is created from might be in an incomplete state when used by `get()`.
     */
    override fun get(): T {
        return getInternal(innerFuture.get())
    }

    /** See [get()]. */
    override fun get(timeout: Long, unit: TimeUnit): T {
        return getInternal(innerFuture.get(timeout, unit))
    }

    /** See [get()]. */
    private fun getInternal(deferred: Deferred<T>): T {
        if (deferred.isCancelled) {
            val exception = deferred.getCompletionExceptionOrNull()
            if (exception is kotlinx.coroutines.CancellationException) {
                throw exception
            } else {
                throw ExecutionException(exception)
            }
        } else {
            return deferred.getCompleted()
        }
    }

    override fun addListener(listener: Runnable, executor: Executor) {
        innerFuture.addListener(listener, executor)
    }

    override fun isDone(): Boolean {
        return innerFuture.isDone
    }

    override fun cancel(mayInterruptIfRunning: Boolean): Boolean {
        return innerFuture.cancel(mayInterruptIfRunning)
    }
}

/**
 * Holds a delegate deferred, and serves as a state machine for [Future] cancellation.
 *
 * [AbstractFuture] has a highly-correct atomic implementation of `Future`'s completion and
 * cancellation semantics. By using that type, the [OuterFuture] can delegate its semantics to
 * _this_ `Future` `get()` the result in such a way that the `Deferred` is always complete when
 * returned.
 */
private class DeferredListenableFuture<T>(
    private val deferred: Deferred<T>
) : AbstractFuture<Deferred<T>>() {

    fun complete() {
        set(deferred)
    }

    /**
     * Tries to cancel the task. This is fundamentally racy.
     *
     * For any given call to `cancel()`, if [deferred] is already completed, the call will complete
     * this Future with it, and fail to cancel. Otherwise, the
     * call to `cancel()` will try to cancel this Future: if and only if cancellation of this
     * succeeds, [deferred] will have its [Deferred.cancel] called.
     *
     * This arrangement means that [deferred] _might not successfully cancel_, if the race resolves
     * in a particular way. [deferred] may also be in its "cancelling" state while this
     * ListenableFuture is complete and cancelled.
     *
     * [OuterFuture] collaborates with this class to present a more cohesive picture and ensure
     * that certain combinations of cancelled/cancelling states can't be observed.
     */
    override fun cancel(mayInterruptIfRunning: Boolean): Boolean {
        return if (super.cancel(mayInterruptIfRunning)) {
            deferred.cancel()
            true
        } else {
            false
        }
    }
}
