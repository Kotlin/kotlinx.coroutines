/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.Job
import kotlinx.coroutines.suspendCancellableCoroutine
import org.reactivestreams.Publisher
import org.reactivestreams.Subscriber
import org.reactivestreams.Subscription
import java.lang.IllegalStateException
import java.util.*
import kotlin.coroutines.*

/**
 * Awaits for the first value from the given publisher without blocking a thread and
 * returns the resulting value or throws the corresponding exception if this publisher had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if publisher does not emit any value
 */
public suspend fun <T> Publisher<T>.awaitFirst(): T = awaitOne(Mode.FIRST)

/**
 * Awaits for the first value from the given observable or the [default] value if none is emitted without blocking a
 * thread and returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> Publisher<T>.awaitFirstOrDefault(default: T): T = awaitOne(Mode.FIRST_OR_DEFAULT, default)

/**
 * Awaits for the first value from the given observable or `null` value if none is emitted without blocking a
 * thread and returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> Publisher<T>.awaitFirstOrNull(): T? = awaitOne(Mode.FIRST_OR_DEFAULT)

/**
 * Awaits for the first value from the given observable or call [defaultValue] to get a value if none is emitted without blocking a
 * thread and returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> Publisher<T>.awaitFirstOrElse(defaultValue: () -> T): T = awaitOne(Mode.FIRST_OR_DEFAULT) ?: defaultValue()

/**
 * Awaits for the last value from the given publisher without blocking a thread and
 * returns the resulting value or throws the corresponding exception if this publisher had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if publisher does not emit any value
 */
public suspend fun <T> Publisher<T>.awaitLast(): T = awaitOne(Mode.LAST)

/**
 * Awaits for the single value from the given publisher without blocking a thread and
 * returns the resulting value or throws the corresponding exception if this publisher had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if publisher does not emit any value
 * @throws IllegalArgumentException if publisher emits more than one value
 */
public suspend fun <T> Publisher<T>.awaitSingle(): T = awaitOne(Mode.SINGLE)

/**
 * Awaits for the single value from the given publisher or the [default] value if none is emitted without blocking a thread and
 * returns the resulting value or throws the corresponding exception if this publisher had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if publisher does not emit any value
 * @throws IllegalArgumentException if publisher emits more than one value
 */
public suspend fun <T> Publisher<T>.awaitSingleOrDefault(default: T): T = awaitOne(Mode.SINGLE_OR_DEFAULT, default)

/**
 * Awaits for the single value from the given publisher or `null` value if none is emitted without blocking a thread and
 * returns the resulting value or throws the corresponding exception if this publisher had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if publisher does not emit any value
 * @throws IllegalArgumentException if publisher emits more than one value
 */
public suspend fun <T> Publisher<T>.awaitSingleOrNull(): T = awaitOne(Mode.SINGLE_OR_DEFAULT)

/**
 * Awaits for the single value from the given publisher or call [defaultValue] to get a value if none is emitted without blocking a thread and
 * returns the resulting value or throws the corresponding exception if this publisher had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if publisher does not emit any value
 * @throws IllegalArgumentException if publisher emits more than one value
 */
public suspend fun <T> Publisher<T>.awaitSingleOrElse(defaultValue: () -> T): T = awaitOne(Mode.SINGLE_OR_DEFAULT) ?: defaultValue()

// ------------------------ private ------------------------

private enum class Mode(val s: String) {
    FIRST("awaitFirst"),
    FIRST_OR_DEFAULT("awaitFirstOrDefault"),
    LAST("awaitLast"),
    SINGLE("awaitSingle"),
    SINGLE_OR_DEFAULT("awaitSingleOrDefault");
    override fun toString(): String = s
}

private suspend fun <T> Publisher<T>.awaitOne(
    mode: Mode,
    default: T? = null
): T = suspendCancellableCoroutine { cont ->
    /* This implementation must obey
    https://github.com/reactive-streams/reactive-streams-jvm/blob/v1.0.3/README.md#2-subscriber-code
    The numbers of rules are taken from there. */
    injectCoroutineContext(cont.context).subscribe(object : Subscriber<T> {
        // It is unclear whether 2.13 implies (T: Any), but if so, it seems that we don't break anything by not adhering
        private var subscription: Subscription? = null
        private var value: T? = null
        private var seenValue = false
        private var inTerminalState = false

        override fun onSubscribe(sub: Subscription) {
            /** cancelling the existing subscription due to rule 2.5, though the publisher would either have to
             * subscribe more than once, which would break 2.12, or leak this [Subscriber]. */
            subscription?.let {
                value = null
                seenValue = false
                inTerminalState = false
                it.cancel()
            }
            subscription = sub
            cont.invokeOnCancellation { sub.cancel() }
            sub.request(if (mode == Mode.FIRST || mode == Mode.FIRST_OR_DEFAULT) 1 else Long.MAX_VALUE)
        }

        override fun onNext(t: T) {
            val sub = subscription.checkInitialized("onNext")
            subscription.checkInitialized("onNext")
            if (inTerminalState)
                gotSignalInTerminalStateException("onNext")
            when (mode) {
                Mode.FIRST, Mode.FIRST_OR_DEFAULT -> {
                    if (seenValue)
                        // TODO: decide if we want to be lenient here: after all, nothing breaks if this isn't true
                        moreThanOneValueProvidedException(mode)
                    seenValue = true
                    sub.cancel()
                    cont.resume(t)
                }
                Mode.LAST, Mode.SINGLE, Mode.SINGLE_OR_DEFAULT -> {
                    if ((mode == Mode.SINGLE || mode == Mode.SINGLE_OR_DEFAULT) && seenValue) {
                        sub.cancel()
                        if (cont.isActive)
                            cont.resumeWithException(IllegalArgumentException("More than one onNext value for $mode"))
                    } else {
                        value = t
                        seenValue = true
                    }
                }
            }
        }

        @Suppress("UNCHECKED_CAST")
        override fun onComplete() {
            subscription.checkInitialized("onComplete") // TODO: maybe don't enforce?
            enterTerminalState("onComplete")
            if (seenValue) {
                if (cont.isActive) cont.resume(value as T)
                return
            }
            when {
                (mode == Mode.FIRST_OR_DEFAULT || mode == Mode.SINGLE_OR_DEFAULT) -> {
                    cont.resume(default as T)
                }
                cont.isActive -> {
                    cont.resumeWithException(NoSuchElementException("No value received via onNext for $mode"))
                }
            }
        }

        override fun onError(e: Throwable) {
            subscription.checkInitialized("onError") // TODO: maybe don't enforce?
            enterTerminalState("onError")
            cont.resumeWithException(e)
        }

        /**
         * Enforce rule 2.4: assume that the [Publisher] is in a terminal state after [onError] or [onComplete].
         */
        private fun enterTerminalState(signalName: String) {
            if (inTerminalState)
                gotSignalInTerminalStateException(signalName)
            inTerminalState = true
        }
    })
}

/**
 * Enforce rule 2.4 (detect publishers that don't respect rule 1.7): don't process anything after a terminal
 * state was reached.
 */
private fun gotSignalInTerminalStateException(signalName: String): Nothing =
    throw IllegalStateException(
        "'$signalName' was called after the publisher already signalled being in a terminal state")

/**
 * Enforce rule 1.1: it is invalid for a publisher to provide more values than requested.
 */
private fun moreThanOneValueProvidedException(mode: Mode): Nothing =
    throw IllegalStateException("Only a single value were requested in $mode, but the publisher provided more")

/**
 * Enforce rule 1.9: expect [Subscriber.onSubscribe] before any other signals.
 */
private fun Subscription?.checkInitialized(signalName: String): Subscription =
    this ?: throw IllegalStateException("'$signalName' was called before 'onSubscribe'")
