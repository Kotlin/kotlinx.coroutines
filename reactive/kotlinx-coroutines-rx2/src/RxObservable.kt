/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.exceptions.*
import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.sync.*
import kotlin.coroutines.*
import kotlin.internal.*

/**
 * Creates cold [observable][Observable] that will run a given [block] in a coroutine.
 * Every time the returned observable is subscribed, it starts a new coroutine.
 *
 * Coroutine emits ([ObservableEmitter.onNext]) values with `send`, completes ([ObservableEmitter.onComplete])
 * when the coroutine completes or channel is explicitly closed and emits error ([ObservableEmitter.onError])
 * if coroutine throws an exception or closes channel with a cause.
 * Unsubscribing cancels running coroutine.
 *
 * Invocations of `send` are suspended appropriately to ensure that `onNext` is not invoked concurrently.
 * Note that Rx 2.x [Observable] **does not support backpressure**.
 *
 * Coroutine context can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * Method throws [IllegalArgumentException] if provided [context] contains a [Job] instance.
 */
@ExperimentalCoroutinesApi
public fun <T : Any> rxObservable(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Observable<T> {
    require(context[Job] === null) { "Observable context cannot contain job in it." +
            "Its lifecycle should be managed via Disposable handle. Had $context" }
    return rxObservableInternal(GlobalScope, context, block)
}

@Deprecated(
    message = "CoroutineScope.rxObservable is deprecated in favour of top-level rxObservable",
    level = DeprecationLevel.ERROR,
    replaceWith = ReplaceWith("rxObservable(context, block)")
) // Since 1.3.0, will be error in 1.3.1 and hidden in 1.4.0
@LowPriorityInOverloadResolution
public fun <T : Any> CoroutineScope.rxObservable(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Observable<T> = rxObservableInternal(this, context, block)

private fun <T : Any> rxObservableInternal(
    scope: CoroutineScope, // support for legacy rxObservable in scope
    context: CoroutineContext,
    block: suspend ProducerScope<T>.() -> Unit
): Observable<T> = Observable.create { subscriber ->
    val newContext = scope.newCoroutineContext(context)
    val coroutine = RxObservableCoroutine(newContext, subscriber)
    subscriber.setCancellable(RxCancellable(coroutine)) // do it first (before starting coroutine), to await unnecessary suspensions
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
}

private const val OPEN = 0        // open channel, still working
private const val CLOSED = -1     // closed, but have not signalled onCompleted/onError yet
private const val SIGNALLED = -2  // already signalled subscriber onCompleted/onError

private class RxObservableCoroutine<T: Any>(
    parentContext: CoroutineContext,
    private val subscriber: ObservableEmitter<T>
) : AbstractCoroutine<Unit>(parentContext, true), ProducerScope<T>, SelectClause2<T, SendChannel<T>> {
    override val channel: SendChannel<T> get() = this

    // Mutex is locked when while subscriber.onXXX is being invoked
    private val mutex = Mutex()

    private val _signal = atomic(OPEN)

    override val isClosedForSend: Boolean get() = isCompleted
    override val isFull: Boolean = mutex.isLocked
    override fun close(cause: Throwable?): Boolean = cancelCoroutine(cause)
    override fun invokeOnClose(handler: (Throwable?) -> Unit) =
        throw UnsupportedOperationException("RxObservableCoroutine doesn't support invokeOnClose")

    override fun offer(element: T): Boolean {
        if (!mutex.tryLock()) return false
        doLockedNext(element)
        return true
    }

    public override suspend fun send(element: T) {
        // fast-path -- try send without suspension
        if (offer(element)) return
        // slow-path does suspend
        return sendSuspend(element)
    }

    private suspend fun sendSuspend(element: T) {
        mutex.lock()
        doLockedNext(element)
    }

    override val onSend: SelectClause2<T, SendChannel<T>>
        get() = this

    // registerSelectSend
    @Suppress("PARAMETER_NAME_CHANGED_ON_OVERRIDE")
    override fun <R> registerSelectClause2(select: SelectInstance<R>, element: T, block: suspend (SendChannel<T>) -> R) {
        mutex.onLock.registerSelectClause2(select, null) {
            doLockedNext(element)
            block(this)
        }
    }

    // assert: mutex.isLocked()
    private fun doLockedNext(elem: T) {
        // check if already closed for send
        if (!isActive) {
            doLockedSignalCompleted(completionCause, completionCauseHandled)
            throw getCancellationException()
        }
        // notify subscriber
        try {
            subscriber.onNext(elem)
        } catch (e: Throwable) {
            // If onNext fails with exception, then we cancel coroutine (with this exception) and then rethrow it
            // to abort the corresponding send/offer invocation. From the standpoint of coroutines machinery,
            // this failure is essentially equivalent to a failure of a child coroutine.
            cancelCoroutine(e)
            mutex.unlock()
            throw e
        }
        /*
         * There is no sense to check for `isActive` before doing `unlock`, because cancellation/completion might
         * happen after this check and before `unlock` (see signalCompleted that does not do anything
         * if it fails to acquire the lock that we are still holding).
         * We have to recheck `isCompleted` after `unlock` anyway.
         */
        unlockAndCheckCompleted()
    }

    private fun unlockAndCheckCompleted() {
        mutex.unlock()
        // recheck isActive
        if (!isActive && mutex.tryLock())
            doLockedSignalCompleted(completionCause, completionCauseHandled)
    }

    // assert: mutex.isLocked()
    private fun doLockedSignalCompleted(cause: Throwable?, handled: Boolean) {
        // cancellation failures
        try {
            if (_signal.value >= CLOSED) {
                _signal.value = SIGNALLED // we'll signal onError/onCompleted (that the final state -- no CAS needed)
                try {
                    if (cause != null && cause !is CancellationException) {
                        /*
                         * Reactive frameworks have two types of exceptions: regular and fatal.
                         * Regular are passed to onError.
                         * Fatal can be passed to onError, but even the standard implementations **can just swallow it** (e.g. see #1297).
                         * Such behaviour is inconsistent, leads to silent failures and we can't possibly know whether
                         * the cause will be handled by onError (and moreover, it depends on whether a fatal exception was
                         * thrown by subscriber or upstream).
                         * To make behaviour consistent and least surprising, we always handle fatal exceptions
                         * by coroutines machinery, anyway, they should not be present in regular program flow,
                         * thus our goal here is just to expose it as soon as possible.
                         */
                        subscriber.tryOnError(cause)
                        if (!handled && cause.isFatal()) {
                            handleUndeliverableException(cause, context)
                        }
                    }
                    else {
                        subscriber.onComplete()
                    }
                } catch (e: Throwable) {
                    // Unhandled exception (cannot handle in other way, since we are already complete)
                    handleUndeliverableException(e, context)
                }
            }
        } finally {
            mutex.unlock()
        }
    }

    private fun signalCompleted(cause: Throwable?, handled: Boolean) {
        if (!_signal.compareAndSet(OPEN, CLOSED)) return // abort, other thread invoked doLockedSignalCompleted
        if (mutex.tryLock()) // if we can acquire the lock
            doLockedSignalCompleted(cause, handled)
    }

    override fun onCompleted(value: Unit) {
        signalCompleted(null, false)
    }

    override fun onCancelled(cause: Throwable, handled: Boolean) {
        signalCompleted(cause, handled)
    }
}

internal fun Throwable.isFatal() = try {
    Exceptions.throwIfFatal(this) // Rx-consistent behaviour without hardcode
    false
} catch (e: Throwable) {
    true
}
