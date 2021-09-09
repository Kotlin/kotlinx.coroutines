/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import org.reactivestreams.Publisher
import org.reactivestreams.Subscriber
import org.reactivestreams.Subscription
import java.lang.IllegalStateException
import kotlin.coroutines.*

/**
 * Awaits the first value from the given publisher without blocking the thread and returns the resulting value, or, if
 * the publisher has produced an error, throws the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Subscription] and resumes with [CancellationException].
 *
 * @throws NoSuchElementException if the publisher does not emit any value
 */
public suspend fun <T> Publisher<T>.awaitFirst(): T = awaitOne(Mode.FIRST)

/**
 * Awaits the first value from the given publisher, or returns the [default] value if none is emitted, without blocking
 * the thread, and returns the resulting value, or, if this publisher has produced an error, throws the corresponding
 * exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Subscription] and resumes with [CancellationException].
 */
public suspend fun <T> Publisher<T>.awaitFirstOrDefault(default: T): T = awaitOne(Mode.FIRST_OR_DEFAULT, default)

/**
 * Awaits the first value from the given publisher, or returns `null` if none is emitted, without blocking the thread,
 * and returns the resulting value, or, if this publisher has produced an error, throws the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Subscription] and resumes with [CancellationException].
 */
public suspend fun <T> Publisher<T>.awaitFirstOrNull(): T? = awaitOne(Mode.FIRST_OR_DEFAULT)

/**
 * Awaits the first value from the given publisher, or calls [defaultValue] to get a value if none is emitted, without
 * blocking the thread, and returns the resulting value, or, if this publisher has produced an error, throws the
 * corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Subscription] and resumes with [CancellationException].
 */
public suspend fun <T> Publisher<T>.awaitFirstOrElse(defaultValue: () -> T): T = awaitOne(Mode.FIRST_OR_DEFAULT) ?: defaultValue()

/**
 * Awaits the last value from the given publisher without blocking the thread and
 * returns the resulting value, or, if this publisher has produced an error, throws the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Subscription] and resumes with [CancellationException].
 *
 * @throws NoSuchElementException if the publisher does not emit any value
 */
public suspend fun <T> Publisher<T>.awaitLast(): T = awaitOne(Mode.LAST)

/**
 * Awaits the single value from the given publisher without blocking the thread and returns the resulting value, or,
 * if this publisher has produced an error, throws the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Subscription] and resumes with [CancellationException].
 *
 * @throws NoSuchElementException if the publisher does not emit any value
 * @throws IllegalArgumentException if the publisher emits more than one value
 */
public suspend fun <T> Publisher<T>.awaitSingle(): T = awaitOne(Mode.SINGLE)

/**
 * Awaits the single value from the given publisher, or returns the [default] value if none is emitted, without
 * blocking the thread, and returns the resulting value, or, if this publisher has produced an error, throws the
 * corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Subscription] and resumes with [CancellationException].
 *
 * ### Deprecation
 *
 * This method is deprecated because the conventions established in Kotlin mandate that an operation with the name
 * `awaitSingleOrDefault` returns the default value instead of throwing in case there is an error; however, this would
 * also mean that this method would return the default value if there are *too many* values. This could be confusing to
 * those who expect this function to validate that there is a single element or none at all emitted, and cases where
 * there are no elements are indistinguishable from those where there are too many, though these cases have different
 * meaning.
 *
 * @throws NoSuchElementException if the publisher does not emit any value
 * @throws IllegalArgumentException if the publisher emits more than one value
 *
 * @suppress
 */
@Deprecated(
    message = "Deprecated without a replacement due to its name incorrectly conveying the behavior. " +
        "Please consider using awaitFirstOrDefault().",
    level = DeprecationLevel.WARNING
) // Warning since 1.5, error in 1.6, hidden in 1.7
public suspend fun <T> Publisher<T>.awaitSingleOrDefault(default: T): T = awaitOne(Mode.SINGLE_OR_DEFAULT, default)

/**
 * Awaits the single value from the given publisher without blocking the thread and returns the resulting value, or, if
 * this publisher has produced an error, throws the corresponding exception. If more than one value or none were
 * produced by the publisher, `null` is returned.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Subscription] and resumes with [CancellationException].
 *
 * ### Deprecation
 *
 * This method is deprecated because the conventions established in Kotlin mandate that an operation with the name
 * `awaitSingleOrNull` returns `null` instead of throwing in case there is an error; however, this would
 * also mean that this method would return `null` if there are *too many* values. This could be confusing to
 * those who expect this function to validate that there is a single element or none at all emitted, and cases where
 * there are no elements are indistinguishable from those where there are too many, though these cases have different
 * meaning.
 *
 * @throws IllegalArgumentException if the publisher emits more than one value
 * @suppress
 */
@Deprecated(
    message = "Deprecated without a replacement due to its name incorrectly conveying the behavior. " +
        "There is a specialized version for Reactor's Mono, please use that where applicable. " +
        "Alternatively, please consider using awaitFirstOrNull().",
    level = DeprecationLevel.WARNING,
    replaceWith = ReplaceWith("this.awaitSingleOrNull()", "kotlinx.coroutines.reactor")
) // Warning since 1.5, error in 1.6, hidden in 1.7
public suspend fun <T> Publisher<T>.awaitSingleOrNull(): T? = awaitOne(Mode.SINGLE_OR_DEFAULT)

/**
 * Awaits the single value from the given publisher, or calls [defaultValue] to get a value if none is emitted, without
 * blocking the thread, and returns the resulting value, or, if this publisher has produced an error, throws the
 * corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately cancels its [Subscription] and resumes with [CancellationException].
 *
 * ### Deprecation
 *
 * This method is deprecated because the conventions established in Kotlin mandate that an operation with the name
 * `awaitSingleOrElse` returns the calculated value instead of throwing in case there is an error; however, this would
 * also mean that this method would return the calculated value if there are *too many* values. This could be confusing
 * to those who expect this function to validate that there is a single element or none at all emitted, and cases where
 * there are no elements are indistinguishable from those where there are too many, though these cases have different
 * meaning.
 *
 * @throws IllegalArgumentException if the publisher emits more than one value
 * @suppress
 */
@Deprecated(
    message = "Deprecated without a replacement due to its name incorrectly conveying the behavior. " +
        "Please consider using awaitFirstOrElse().",
    level = DeprecationLevel.WARNING
) // Warning since 1.5, error in 1.6, hidden in 1.7
public suspend fun <T> Publisher<T>.awaitSingleOrElse(defaultValue: () -> T): T =
    awaitOne(Mode.SINGLE_OR_DEFAULT) ?: defaultValue()

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
            /** cancelling the new subscription due to rule 2.5, though the publisher would either have to
             * subscribe more than once, which would break 2.12, or leak this [Subscriber]. */
            if (subscription != null) {
                sub.cancel()
                return
            }
            subscription = sub
            cont.invokeOnCancellation { sub.cancel() }
            sub.request(if (mode == Mode.FIRST || mode == Mode.FIRST_OR_DEFAULT) 1 else Long.MAX_VALUE)
        }

        override fun onNext(t: T) {
            val sub = subscription.let {
                if (it == null) {
                    /** Enforce rule 1.9: expect [Subscriber.onSubscribe] before any other signals. */
                    handleCoroutineException(cont.context,
                        IllegalStateException("'onNext' was called before 'onSubscribe'"))
                    return
                } else {
                    it
                }
            }
            if (inTerminalState) {
                gotSignalInTerminalStateException(cont.context, "onNext")
                return
            }
            when (mode) {
                Mode.FIRST, Mode.FIRST_OR_DEFAULT -> {
                    if (seenValue) {
                        moreThanOneValueProvidedException(cont.context, mode)
                        return
                    }
                    seenValue = true
                    sub.cancel()
                    cont.resume(t)
                }
                Mode.LAST, Mode.SINGLE, Mode.SINGLE_OR_DEFAULT -> {
                    if ((mode == Mode.SINGLE || mode == Mode.SINGLE_OR_DEFAULT) && seenValue) {
                        sub.cancel()
                        /* the check for `cont.isActive` is needed in case `sub.cancel() above calls `onComplete` or
                         `onError` on its own. */
                        if (cont.isActive) {
                            cont.resumeWithException(IllegalArgumentException("More than one onNext value for $mode"))
                        }
                    } else {
                        value = t
                        seenValue = true
                    }
                }
            }
        }

        @Suppress("UNCHECKED_CAST")
        override fun onComplete() {
            if (!tryEnterTerminalState("onComplete")) {
                return
            }
            if (seenValue) {
                /* the check for `cont.isActive` is needed because, otherwise, if the publisher doesn't acknowledge the
                call to `cancel` for modes `SINGLE*` when more than one value was seen, it may call `onComplete`, and
                here `cont.resume` would fail. */
                if (mode != Mode.FIRST_OR_DEFAULT && mode != Mode.FIRST && cont.isActive) {
                    cont.resume(value as T)
                }
                return
            }
            when {
                (mode == Mode.FIRST_OR_DEFAULT || mode == Mode.SINGLE_OR_DEFAULT) -> {
                    cont.resume(default as T)
                }
                cont.isActive -> {
                    // the check for `cont.isActive` is just a slight optimization and doesn't affect correctness
                    cont.resumeWithException(NoSuchElementException("No value received via onNext for $mode"))
                }
            }
        }

        override fun onError(e: Throwable) {
            if (tryEnterTerminalState("onError")) {
                cont.resumeWithException(e)
            }
        }

        /**
         * Enforce rule 2.4: assume that the [Publisher] is in a terminal state after [onError] or [onComplete].
         */
        private fun tryEnterTerminalState(signalName: String): Boolean {
            if (inTerminalState) {
                gotSignalInTerminalStateException(cont.context, signalName)
                return false
            }
            inTerminalState = true
            return true
        }
    })
}

/**
 * Enforce rule 2.4 (detect publishers that don't respect rule 1.7): don't process anything after a terminal
 * state was reached.
 */
private fun gotSignalInTerminalStateException(context: CoroutineContext, signalName: String) =
    handleCoroutineException(context,
        IllegalStateException("'$signalName' was called after the publisher already signalled being in a terminal state"))

/**
 * Enforce rule 1.1: it is invalid for a publisher to provide more values than requested.
 */
private fun moreThanOneValueProvidedException(context: CoroutineContext, mode: Mode) =
    handleCoroutineException(context,
        IllegalStateException("Only a single value was requested in '$mode', but the publisher provided more"))
