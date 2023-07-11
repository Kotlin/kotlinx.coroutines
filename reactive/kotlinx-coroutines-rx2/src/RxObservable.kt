/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.exceptions.*
import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.sync.*
import kotlin.coroutines.*

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
public fun <T : Any> rxObservable(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Observable<T> {
    require(context[Job] === null) { "Observable context cannot contain job in it." +
            "Its lifecycle should be managed via Disposable handle. Had $context" }
    return rxObservableInternal(GlobalScope, context, block)
}

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

private class RxObservableCoroutine<T : Any>(
    parentContext: CoroutineContext,
    private val subscriber: ObservableEmitter<T>
) : AbstractCoroutine<Unit>(parentContext, false, true), ProducerScope<T> {
    override val channel: SendChannel<T> get() = this

    private val _signal = atomic(OPEN)

    override val isClosedForSend: Boolean get() = !isActive
    override fun close(cause: Throwable?): Boolean = cancelCoroutine(cause)
    override fun invokeOnClose(handler: (Throwable?) -> Unit) =
        throw UnsupportedOperationException("RxObservableCoroutine doesn't support invokeOnClose")

    // Mutex is locked when either nRequested == 0 or while subscriber.onXXX is being invoked
    private val mutex: Mutex = Mutex()

    @Suppress("UNCHECKED_CAST", "INVISIBLE_MEMBER")
    override val onSend: SelectClause2<T, SendChannel<T>> get() = SelectClause2Impl(
        clauseObject = this,
        regFunc = RxObservableCoroutine<*>::registerSelectForSend as RegistrationFunction,
        processResFunc = RxObservableCoroutine<*>::processResultSelectSend as ProcessResultFunction
    )

    @Suppress("UNUSED_PARAMETER")
    private fun registerSelectForSend(select: SelectInstance<*>, element: Any?) {
        // Try to acquire the mutex and complete in the registration phase.
        if (mutex.tryLock()) {
            select.selectInRegistrationPhase(Unit)
            return
        }
        // Start a new coroutine that waits for the mutex, invoking `trySelect(..)` after that.
        // Please note that at the point of the `trySelect(..)` invocation the corresponding
        // `select` can still be in the registration phase, making this `trySelect(..)` bound to fail.
        // In this case, the `onSend` clause will be re-registered, which alongside with the mutex
        // manipulation makes the resulting solution obstruction-free.
        launch {
            mutex.lock()
            if (!select.trySelect(this@RxObservableCoroutine, Unit)) {
                mutex.unlock()
            }
        }
    }

    @Suppress("RedundantNullableReturnType", "UNUSED_PARAMETER", "UNCHECKED_CAST")
    private fun processResultSelectSend(element: Any?, selectResult: Any?): Any? {
        doLockedNext(element as T)?.let { throw it }
        return this@RxObservableCoroutine
    }

    override fun trySend(element: T): ChannelResult<Unit> =
        if (!mutex.tryLock()) {
            ChannelResult.failure()
        } else {
            when (val throwable = doLockedNext(element)) {
                null -> ChannelResult.success(Unit)
                else -> ChannelResult.closed(throwable)
            }
        }

    override suspend fun send(element: T) {
        mutex.lock()
        doLockedNext(element)?.let { throw it }
    }

    // assert: mutex.isLocked()
    private fun doLockedNext(elem: T): Throwable? {
        // check if already closed for send
        if (!isActive) {
            doLockedSignalCompleted(completionCause, completionCauseHandled)
            return getCancellationException()
        }
        // notify subscriber
        try {
            subscriber.onNext(elem)
        } catch (e: Throwable) {
            val cause = UndeliverableException(e)
            val causeDelivered = close(cause)
            unlockAndCheckCompleted()
            return if (causeDelivered) {
                // `cause` is the reason this channel is closed
                cause
            } else {
                // Someone else closed the channel during `onNext`. We report `cause` as an undeliverable exception.
                handleUndeliverableException(cause, context)
                getCancellationException()
            }
        }
        /*
         * There is no sense to check for `isActive` before doing `unlock`, because cancellation/completion might
         * happen after this check and before `unlock` (see signalCompleted that does not do anything
         * if it fails to acquire the lock that we are still holding).
         * We have to recheck `isCompleted` after `unlock` anyway.
         */
        unlockAndCheckCompleted()
        return null
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
            if (_signal.value == SIGNALLED)
                return
            _signal.value = SIGNALLED // we'll signal onError/onCompleted (that the final state -- no CAS needed)
            @Suppress("INVISIBLE_MEMBER")
            val unwrappedCause = cause?.let { unwrap(it) }
            if (unwrappedCause == null) {
                try {
                    subscriber.onComplete()
                } catch (e: Exception) {
                    handleUndeliverableException(e, context)
                }
            } else if (unwrappedCause is UndeliverableException && !handled) {
                /** Such exceptions are not reported to `onError`, as, according to the reactive specifications,
                 * exceptions thrown from the Subscriber methods must be treated as if the Subscriber was already
                 * cancelled. */
                handleUndeliverableException(cause, context)
            } else if (unwrappedCause !== getCancellationException() || !subscriber.isDisposed) {
                try {
                    /** If the subscriber is already in a terminal state, the error will be signalled to
                     * `RxJavaPlugins.onError`. */
                    subscriber.onError(cause)
                } catch (e: Exception) {
                    cause.addSuppressed(e)
                    handleUndeliverableException(cause, context)
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

/** @suppress */
@Deprecated(
    message = "CoroutineScope.rxObservable is deprecated in favour of top-level rxObservable",
    level = DeprecationLevel.HIDDEN,
    replaceWith = ReplaceWith("rxObservable(context, block)")
) // Since 1.3.0, will be error in 1.3.1 and hidden in 1.4.0
public fun <T : Any> CoroutineScope.rxObservable(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Observable<T> = rxObservableInternal(this, context, block)
