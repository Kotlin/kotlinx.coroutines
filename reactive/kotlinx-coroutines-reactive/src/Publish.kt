/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.reactive

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.sync.*
import org.reactivestreams.*
import kotlin.coroutines.*
import kotlin.internal.LowPriorityInOverloadResolution

/**
 * Creates cold reactive [Publisher] that runs a given [block] in a coroutine.
 * Every time the returned flux is subscribed, it starts a new coroutine in the specified [context].
 * Coroutine emits ([Subscriber.onNext]) values with `send`, completes ([Subscriber.onComplete])
 * when the coroutine completes or channel is explicitly closed and emits error ([Subscriber.onError])
 * if coroutine throws an exception or closes channel with a cause.
 * Unsubscribing cancels running coroutine.
 *
 * Invocations of `send` are suspended appropriately when subscribers apply back-pressure and to ensure that
 * `onNext` is not invoked concurrently.
 *
 * Coroutine context can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * Method throws [IllegalArgumentException] if provided [context] contains a [Job] instance.
 *
 * **Note: This is an experimental api.** Behaviour of publishers that work as children in a parent scope with respect
 *        to cancellation and error handling may change in the future.
 */
@ExperimentalCoroutinesApi
public fun <T> publish(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Publisher<T> {
    require(context[Job] === null) { "Publisher context cannot contain job in it." +
            "Its lifecycle should be managed via subscription. Had $context" }
    return publishInternal(GlobalScope, context, DEFAULT_HANDLER, block)
}

@Deprecated(
    message = "CoroutineScope.publish is deprecated in favour of top-level publish",
    level = DeprecationLevel.ERROR,
    replaceWith = ReplaceWith("publish(context, block)")
) // Since 1.3.0, will be error in 1.3.1 and hidden in 1.4.0. Binary compatibility with Spring
@LowPriorityInOverloadResolution
public fun <T> CoroutineScope.publish(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Publisher<T> = publishInternal(this, context, DEFAULT_HANDLER ,block)

/** @suppress For internal use from other reactive integration modules only */
@InternalCoroutinesApi
public fun <T> publishInternal(
    scope: CoroutineScope, // support for legacy publish in scope
    context: CoroutineContext,
    exceptionOnCancelHandler: (Throwable, CoroutineContext) -> Unit,
    block: suspend ProducerScope<T>.() -> Unit
): Publisher<T> = Publisher { subscriber ->
    // specification requires NPE on null subscriber
    if (subscriber == null) throw NullPointerException("Subscriber cannot be null")
    val newContext = scope.newCoroutineContext(context)
    val coroutine = PublisherCoroutine(newContext, subscriber, exceptionOnCancelHandler)
    subscriber.onSubscribe(coroutine) // do it first (before starting coroutine), to avoid unnecessary suspensions
    coroutine.start(CoroutineStart.DEFAULT, coroutine, block)
}

private const val CLOSED = -1L    // closed, but have not signalled onCompleted/onError yet
private const val SIGNALLED = -2L  // already signalled subscriber onCompleted/onError
private val DEFAULT_HANDLER: (Throwable, CoroutineContext) -> Unit = { t, ctx -> if (t !is CancellationException) handleCoroutineException(ctx, t) }

@Suppress("CONFLICTING_JVM_DECLARATIONS", "RETURN_TYPE_MISMATCH_ON_INHERITANCE")
@InternalCoroutinesApi
public class PublisherCoroutine<in T>(
    parentContext: CoroutineContext,
    private val subscriber: Subscriber<T>,
    private val exceptionOnCancelHandler: (Throwable, CoroutineContext) -> Unit
) : AbstractCoroutine<Unit>(parentContext, true), ProducerScope<T>, Subscription, SelectClause2<T, SendChannel<T>> {
    override val channel: SendChannel<T> get() = this

    // Mutex is locked when either nRequested == 0 or while subscriber.onXXX is being invoked
    private val mutex = Mutex(locked = true)
    private val _nRequested = atomic(0L) // < 0 when closed (CLOSED or SIGNALLED)

    @Volatile
    private var cancelled = false // true when Subscription.cancel() is invoked

    override val isClosedForSend: Boolean get() = isCompleted
    override val isFull: Boolean = mutex.isLocked
    override fun close(cause: Throwable?): Boolean = cancelCoroutine(cause)
    override fun invokeOnClose(handler: (Throwable?) -> Unit) =
        throw UnsupportedOperationException("PublisherCoroutine doesn't support invokeOnClose")

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

    /*
     * This code is not trivial because of the two properties:
     * 1. It ensures conformance to the reactive specification that mandates that onXXX invocations should not
     *    be concurrent. It uses Mutex to protect all onXXX invocation and ensure conformance even when multiple
     *    coroutines are invoking `send` function.
     * 2. Normally, `onComplete/onError` notification is sent only when coroutine and all its children are complete.
     *    However, nothing prevents `publish` coroutine from leaking reference to it send channel to some
     *    globally-scoped coroutine that is invoking `send` outside of this context. Without extra precaution this may
     *    lead to `onNext` that is concurrent with `onComplete/onError`, so that is why signalling for
     *    `onComplete/onError` is also done under the same mutex.
     */

    // assert: mutex.isLocked()
    private fun doLockedNext(elem: T) {
        // check if already closed for send, note that isActive becomes false as soon as cancel() is invoked,
        // because the job is cancelled, so this check also ensure conformance to the reactive specification's
        // requirement that after cancellation requested we don't call onXXX
        if (!isActive) {
            unlockAndCheckCompleted()
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
            unlockAndCheckCompleted()
            throw e
        }
        // now update nRequested
        while (true) { // lock-free loop on nRequested
            val current = _nRequested.value
            if (current < 0) break // closed from inside onNext => unlock
            if (current == Long.MAX_VALUE) break // no back-pressure => unlock
            val updated = current - 1
            if (_nRequested.compareAndSet(current, updated)) {
                if (updated == 0L) {
                    // return to keep locked due to back-pressure
                    return
                }
                break // unlock if updated > 0
            }
        }
        unlockAndCheckCompleted()
    }

    private fun unlockAndCheckCompleted() {
       /*
        * There is no sense to check completion before doing `unlock`, because completion might
        * happen after this check and before `unlock` (see `signalCompleted` that does not do anything
        * if it fails to acquire the lock that we are still holding).
        * We have to recheck `isCompleted` after `unlock` anyway.
        */
        mutex.unlock()
        // check isCompleted and and try to regain lock to signal completion
        if (isCompleted && mutex.tryLock()) {
            doLockedSignalCompleted(completionCause, completionCauseHandled)
        }
    }

    // assert: mutex.isLocked() & isCompleted
    private fun doLockedSignalCompleted(cause: Throwable?, handled: Boolean) {
        try {
            if (_nRequested.value >= CLOSED) {
                _nRequested.value = SIGNALLED // we'll signal onError/onCompleted (that the final state -- no CAS needed)
                // Specification requires that after cancellation requested we don't call onXXX
                if (cancelled) {
                    // If the parent had failed to handle our exception, then we must not lose this exception
                    if (cause != null && !handled) exceptionOnCancelHandler(cause, context)
                    return
                }

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
                        subscriber.onError(cause)
                        if (!handled && cause.isFatal()) {
                            exceptionOnCancelHandler(cause, context)
                        }
                    } else {
                        subscriber.onComplete()
                    }
                } catch (e: Throwable) {
                    handleCoroutineException(context, e)
                }
            }
        } finally {
            mutex.unlock()
        }
    }

    override fun request(n: Long) {
        if (n <= 0) {
            // Specification requires IAE for n <= 0
            cancelCoroutine(IllegalArgumentException("non-positive subscription request $n"))
            return
        }
        while (true) { // lock-free loop for nRequested
            val cur = _nRequested.value
            if (cur < 0) return // already closed for send, ignore requests
            var upd = cur + n
            if (upd < 0 || n == Long.MAX_VALUE)
                upd = Long.MAX_VALUE
            if (cur == upd) return // nothing to do
            if (_nRequested.compareAndSet(cur, upd)) {
                // unlock the mutex when we don't have back-pressure anymore
                if (cur == 0L) {
                    unlockAndCheckCompleted()
                }
                return
            }
        }
    }

    // assert: isCompleted
    private fun signalCompleted(cause: Throwable?, handled: Boolean) {
        while (true) { // lock-free loop for nRequested
            val current = _nRequested.value
            if (current == SIGNALLED) return // some other thread holding lock already signalled cancellation/completion
            check(current >= 0) // no other thread could have marked it as CLOSED, because onCompleted[Exceptionally] is invoked once
            if (!_nRequested.compareAndSet(current, CLOSED)) continue // retry on failed CAS
            // Ok -- marked as CLOSED, now can unlock the mutex if it was locked due to backpressure
            if (current == 0L) {
                doLockedSignalCompleted(cause, handled)
            } else {
                // otherwise mutex was either not locked or locked in concurrent onNext... try lock it to signal completion
                if (mutex.tryLock()) doLockedSignalCompleted(cause, handled)
                // Note: if failed `tryLock`, then `doLockedNext` will signal after performing `unlock`
            }
            return // done anyway
        }
    }

    override fun onCompleted(value: Unit) {
        signalCompleted(null, false)
    }

    override fun onCancelled(cause: Throwable, handled: Boolean) {
        signalCompleted(cause, handled)
    }

    override fun cancel() {
        // Specification requires that after cancellation publisher stops signalling
        // This flag distinguishes subscription cancellation request from the job crash
        cancelled = true
        super.cancel(null)
    }

    private fun Throwable.isFatal() = this is VirtualMachineError || this is ThreadDeath || this is LinkageError
}
