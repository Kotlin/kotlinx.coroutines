/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.*
import io.reactivex.functions.*
import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.selects.*
import kotlinx.coroutines.experimental.sync.*
import kotlin.coroutines.experimental.*

/**
 * Creates cold [observable][Observable] that will run a given [block] in a coroutine.
 * Every time the returned observable is subscribed, it starts a new coroutine.
 * Coroutine emits items with `send`. Unsubscribing cancels running coroutine.
 *
 * Invocations of `send` are suspended appropriately to ensure that `onNext` is not invoked concurrently.
 * Note, that Rx 2.x [Observable] **does not support backpressure**. Use [rxFlowable].
 *
 * | **Coroutine action**                         | **Signal to subscriber**
 * | -------------------------------------------- | ------------------------
 * | `send`                                       | `onNext`
 * | Normal completion or `close` without cause   | `onComplete`
 * | Failure with exception or `close` with cause | `onError`
 *
 * The [context] for the new coroutine can be explicitly specified.
 * See [CoroutineDispatcher] for the standard context implementations that are provided by `kotlinx.coroutines`.
 * The [coroutineContext] of the parent coroutine may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 * The parent job may be also explicitly specified using [parent] parameter.
 *
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param parent explicitly specifies the parent job, overrides job from the [context] (if any).
 * @param block the coroutine code.
 */
public fun <T> rxObservable(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    block: suspend ProducerScope<T>.() -> Unit
): Observable<T> = Observable.create { subscriber ->
    val newContext = newCoroutineContext(context, parent)
    val coroutine = RxObservableCoroutine(newContext, subscriber)
    subscriber.setCancellable(coroutine) // do it first (before starting coroutine), to await unnecessary suspensions
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
}

/** @suppress **Deprecated**: Binary compatibility */
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
@JvmOverloads // for binary compatibility with older code compiled before context had a default
public fun <T> rxObservable(
    context: CoroutineContext = DefaultDispatcher,
    block: suspend ProducerScope<T>.() -> Unit
): Observable<T> =
    rxObservable(context, block = block)

private const val OPEN = 0        // open channel, still working
private const val CLOSED = -1     // closed, but have not signalled onCompleted/onError yet
private const val SIGNALLED = -2  // already signalled subscriber onCompleted/onError

private class RxObservableCoroutine<T>(
    parentContext: CoroutineContext,
    private val subscriber: ObservableEmitter<T>
) : AbstractCoroutine<Unit>(parentContext, true), ProducerScope<T>, Cancellable, SelectClause2<T, SendChannel<T>> {
    override val channel: SendChannel<T> get() = this

    // Mutex is locked when while subscriber.onXXX is being invoked
    private val mutex = Mutex()

    private val _signal = atomic(OPEN)

    override val isClosedForSend: Boolean get() = isCompleted
    override val isFull: Boolean = mutex.isLocked
    override fun close(cause: Throwable?): Boolean = cancel(cause)
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
            doLockedSignalCompleted()
            throw getCancellationException()
        }
        // notify subscriber
        try {
            subscriber.onNext(elem)
        } catch (e: Throwable) {
            try {
                if (!cancel(e))
                    handleCoroutineException(context, e)
            } finally {
                doLockedSignalCompleted()
            }
            throw getCancellationException()
        }
        /*
           There is no sense to check for `isActive` before doing `unlock`, because cancellation/completion might
           happen after this check and before `unlock` (see `onCancellation` that does not do anything
           if it fails to acquire the lock that we are still holding).
           We have to recheck `isCompleted` after `unlock` anyway.
         */
        mutex.unlock()
        // recheck isActive
        if (!isActive && mutex.tryLock())
            doLockedSignalCompleted()
    }

    // assert: mutex.isLocked()
    private fun doLockedSignalCompleted() {
        try {
            if (_signal.value >= CLOSED) {
                _signal.value = SIGNALLED // we'll signal onError/onCompleted (that the final state -- no CAS needed)
                val cause = getCompletionCause()
                try {
                    if (cause != null && cause !is CancellationException)
                        subscriber.onError(cause)
                    else
                        subscriber.onComplete()
                } catch (e: Throwable) {
                    handleCoroutineException(context, e)
                }
            }
        } finally {
            mutex.unlock()
        }
    }

    override fun onCancellation(cause: Throwable?) {
        if (!_signal.compareAndSet(OPEN, CLOSED)) return // abort, other thread invoked doLockedSignalCompleted
        if (mutex.tryLock()) // if we can acquire the lock
            doLockedSignalCompleted()
    }

    // Cancellable impl
    override fun cancel() { cancel(cause = null) }
}