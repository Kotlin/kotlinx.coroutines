/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.reactive

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.sync.*
import org.reactivestreams.*
import kotlin.coroutines.*

/**
 * Creates a cold reactive [Publisher] that runs a given [block] in a coroutine.
 *
 * Every time the returned flux is subscribed, it starts a new coroutine in the specified [context].
 * The coroutine emits (via [Subscriber.onNext]) values with [send][ProducerScope.send],
 * completes (via [Subscriber.onComplete]) when the coroutine completes or channel is explicitly closed, and emits
 * errors (via [Subscriber.onError]) if the coroutine throws an exception or closes channel with a cause.
 * Unsubscribing cancels the running coroutine.
 *
 * Invocations of [send][ProducerScope.send] are suspended appropriately when subscribers apply back-pressure and to
 * ensure that [onNext][Subscriber.onNext] is not invoked concurrently.
 *
 * Coroutine context can be specified with [context] argument.
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [Dispatchers.Default] is
 * used.
 *
 * **Note: This is an experimental api.** Behaviour of publishers that work as children in a parent scope with respect
 *        to cancellation and error handling may change in the future.
 *
 * @throws IllegalArgumentException if the provided [context] contains a [Job] instance.
 */
public fun <T> publish(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Publisher<T> {
    require(context[Job] === null) { "Publisher context cannot contain job in it." +
            "Its lifecycle should be managed via subscription. Had $context" }
    return publishInternal(GlobalScope, context, DEFAULT_HANDLER, block)
}

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

/** @suppress */
@Suppress("CONFLICTING_JVM_DECLARATIONS", "RETURN_TYPE_MISMATCH_ON_INHERITANCE")
@InternalCoroutinesApi
public class PublisherCoroutine<in T>(
    parentContext: CoroutineContext,
    private val subscriber: Subscriber<T>,
    private val exceptionOnCancelHandler: (Throwable, CoroutineContext) -> Unit
) : AbstractCoroutine<Unit>(parentContext, false, true), ProducerScope<T>, Subscription {
    override val channel: SendChannel<T> get() = this

    private val _nRequested = atomic(0L) // < 0 when closed (CLOSED or SIGNALLED)

    @Volatile
    private var cancelled = false // true after Subscription.cancel() is invoked

    override val isClosedForSend: Boolean get() = !isActive
    override fun close(cause: Throwable?): Boolean = cancelCoroutine(cause)
    override fun invokeOnClose(handler: (Throwable?) -> Unit): Nothing =
        throw UnsupportedOperationException("PublisherCoroutine doesn't support invokeOnClose")

    // Mutex is locked when either nRequested == 0 or while subscriber.onXXX is being invoked
    private val mutex: Mutex = Mutex(locked = true)

    @Suppress("UNCHECKED_CAST", "INVISIBLE_MEMBER")
    override val onSend: SelectClause2<T, SendChannel<T>> get() = SelectClause2Impl(
        clauseObject = this,
        regFunc = PublisherCoroutine<*>::registerSelectForSend as RegistrationFunction,
        processResFunc = PublisherCoroutine<*>::processResultSelectSend as ProcessResultFunction
    )

    @Suppress("UNCHECKED_CAST", "UNUSED_PARAMETER")
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
            if (!select.trySelect(this@PublisherCoroutine, Unit)) {
                mutex.unlock()
            }
        }
    }

    @Suppress("RedundantNullableReturnType", "UNUSED_PARAMETER", "UNCHECKED_CAST")
    private fun processResultSelectSend(element: Any?, selectResult: Any?): Any? {
        doLockedNext(element as T)?.let { throw it }
        return this@PublisherCoroutine
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

    public override suspend fun send(element: T) {
        mutex.lock()
        doLockedNext(element)?.let { throw it }
    }

    /*
     * This code is not trivial because of the following properties:
     * 1. It ensures conformance to the reactive specification that mandates that onXXX invocations should not
     *    be concurrent. It uses Mutex to protect all onXXX invocation and ensure conformance even when multiple
     *    coroutines are invoking `send` function.
     * 2. Normally, `onComplete/onError` notification is sent only when coroutine and all its children are complete.
     *    However, nothing prevents `publish` coroutine from leaking reference to it send channel to some
     *    globally-scoped coroutine that is invoking `send` outside of this context. Without extra precaution this may
     *    lead to `onNext` that is concurrent with `onComplete/onError`, so that is why signalling for
     *    `onComplete/onError` is also done under the same mutex.
     * 3. The reactive specification forbids emitting more elements than requested, so `onNext` is forbidden until the
     *    subscriber actually requests some elements. This is implemented by the mutex being locked when emitting
     *    elements is not permitted (`_nRequested.value == 0`).
     */

    /**
     * Attempts to emit a value to the subscriber and, if back-pressure permits this, unlock the mutex.
     *
     * Requires that the caller has locked the mutex before this invocation.
     *
     * If the channel is closed, returns the corresponding [Throwable]; otherwise, returns `null` to denote success.
     *
     * @throws NullPointerException if the passed element is `null`
     */
    private fun doLockedNext(elem: T): Throwable? {
        if (elem == null) {
            unlockAndCheckCompleted()
            throw NullPointerException("Attempted to emit `null` inside a reactive publisher")
        }
        /** This guards against the case when the caller of this function managed to lock the mutex not because some
         * elements were requested--and thus it is permitted to call `onNext`--but because the channel was closed.
         *
         * It may look like there is a race condition here between `isActive` and a concurrent cancellation, but it's
         * okay for a cancellation to happen during `onNext`, as the reactive spec only requires that we *eventually*
         * stop signalling the subscriber. */
        if (!isActive) {
            unlockAndCheckCompleted()
            return getCancellationException()
        }
        // notify the subscriber
        try {
            subscriber.onNext(elem)
        } catch (cause: Throwable) {
            /** The reactive streams spec forbids the subscribers from throwing from [Subscriber.onNext] unless the
             * element is `null`, which we check not to be the case. Therefore, we report this exception to the handler
             * for uncaught exceptions and consider the subscription cancelled, as mandated by
             * https://github.com/reactive-streams/reactive-streams-jvm/blob/v1.0.3/README.md#2.13.
             *
             * Some reactive implementations, like RxJava or Reactor, are known to throw from [Subscriber.onNext] if the
             * execution encounters an exception they consider to be "fatal", like [VirtualMachineError] or
             * [ThreadDeath]. Us using the handler for the undeliverable exceptions to signal "fatal" exceptions is
             * inconsistent with RxJava and Reactor, which attempt to bubble the exception up the call chain as soon as
             * possible. However, we can't do much better here, as simply throwing from all methods indiscriminately
             * would violate the contracts we place on them. */
            cancelled = true
            val causeDelivered = close(cause)
            unlockAndCheckCompleted()
            return if (causeDelivered) {
                // `cause` is the reason this channel is closed
                cause
            } else {
                // Someone else closed the channel during `onNext`. We report `cause` as an undeliverable exception.
                exceptionOnCancelHandler(cause, context)
                getCancellationException()
            }
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
                    return null
                }
                break // unlock if updated > 0
            }
        }
        unlockAndCheckCompleted()
        return null
    }

    private fun unlockAndCheckCompleted() {
       /*
        * There is no sense to check completion before doing `unlock`, because completion might
        * happen after this check and before `unlock` (see `signalCompleted` that does not do anything
        * if it fails to acquire the lock that we are still holding).
        * We have to recheck `isCompleted` after `unlock` anyway.
        */
        mutex.unlock()
        // check isCompleted and try to regain lock to signal completion
        if (isCompleted && mutex.tryLock()) {
            doLockedSignalCompleted(completionCause, completionCauseHandled)
        }
    }

    // assert: mutex.isLocked() & isCompleted
    private fun doLockedSignalCompleted(cause: Throwable?, handled: Boolean) {
        try {
            if (_nRequested.value == SIGNALLED)
                return
            _nRequested.value = SIGNALLED // we'll signal onError/onCompleted (the final state, so no CAS needed)
            // Specification requires that after the cancellation is requested we eventually stop calling onXXX
            if (cancelled) {
                // If the parent failed to handle this exception, then we must not lose the exception
                if (cause != null && !handled) exceptionOnCancelHandler(cause, context)
                return
            }
            if (cause == null) {
                try {
                    subscriber.onComplete()
                } catch (e: Throwable) {
                    handleCoroutineException(context, e)
                }
            } else {
                try {
                    // This can't be the cancellation exception from `cancel`, as then `cancelled` would be `true`.
                    subscriber.onError(cause)
                } catch (e: Throwable) {
                    if (e !== cause) {
                        cause.addSuppressed(e)
                    }
                    handleCoroutineException(context, cause)
                }
            }
        } finally {
            mutex.unlock()
        }
    }

    override fun request(n: Long) {
        if (n <= 0) {
            // Specification requires to call onError with IAE for n <= 0
            cancelCoroutine(IllegalArgumentException("non-positive subscription request $n"))
            return
        }
        while (true) { // lock-free loop for nRequested
            val cur = _nRequested.value
            if (cur < 0) return // already closed for send, ignore requests, as mandated by the reactive streams spec
            var upd = cur + n
            if (upd < 0 || n == Long.MAX_VALUE)
                upd = Long.MAX_VALUE
            if (cur == upd) return // nothing to do
            if (_nRequested.compareAndSet(cur, upd)) {
                // unlock the mutex when we don't have back-pressure anymore
                if (cur == 0L) {
                    /** In a sense, after a successful CAS, it is this invocation, not the coroutine itself, that owns
                     * the lock, given that `upd` is necessarily strictly positive. Thus, no other operation has the
                     * right to lower the value on [_nRequested], it can only grow or become [CLOSED]. Therefore, it is
                     * impossible for any other operations to assume that they own the lock without actually acquiring
                     * it. */
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
}

@Deprecated(
    message = "CoroutineScope.publish is deprecated in favour of top-level publish",
    level = DeprecationLevel.HIDDEN,
    replaceWith = ReplaceWith("publish(context, block)")
) // Since 1.3.0, will be error in 1.3.1 and hidden in 1.4.0. Binary compatibility with Spring
public fun <T> CoroutineScope.publish(
    context: CoroutineContext = EmptyCoroutineContext,
    @BuilderInference block: suspend ProducerScope<T>.() -> Unit
): Publisher<T> = publishInternal(this, context, DEFAULT_HANDLER, block)
