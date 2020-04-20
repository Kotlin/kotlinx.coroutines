/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import io.reactivex.rxjava3.core.*
import io.reactivex.rxjava3.disposables.Disposable
import kotlinx.coroutines.CancellableContinuation
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.Job
import kotlinx.coroutines.suspendCancellableCoroutine
import kotlin.coroutines.*

// ------------------------ CompletableSource ------------------------

/**
 * Awaits for completion of this completable without blocking a thread.
 * Returns `Unit` or throws the corresponding exception if this completable had produced error.
 *
 * This suspending function is cancellable. If the [Job] of the invoking coroutine is cancelled or completed while this
 * suspending function is suspended, this function immediately resumes with [CancellationException].
 */
public suspend fun CompletableSource.await(): Unit = suspendCancellableCoroutine { cont ->
    subscribe(object : CompletableObserver {
        override fun onSubscribe(d: Disposable) { cont.disposeOnCancellation(d) }
        override fun onComplete() { cont.resume(Unit) }
        override fun onError(e: Throwable) { cont.resumeWithException(e) }
    })
}

// ------------------------ MaybeSource ------------------------

/**
 * Awaits for completion of the maybe without blocking a thread.
 * Returns the resulting value, null if no value was produced or throws the corresponding exception if this
 * maybe had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
@Suppress("UNCHECKED_CAST")
public suspend fun <T> MaybeSource<T>.await(): T? = (this as MaybeSource<T?>).awaitOrDefault(null)

/**
 * Awaits for completion of the maybe without blocking a thread.
 * Returns the resulting value, [default] if no value was produced or throws the corresponding exception if this
 * maybe had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> MaybeSource<T>.awaitOrDefault(default: T): T = suspendCancellableCoroutine { cont ->
    subscribe(object : MaybeObserver<T> {
        override fun onSubscribe(d: Disposable) { cont.disposeOnCancellation(d) }
        override fun onComplete() { cont.resume(default) }
        override fun onSuccess(t: T) { cont.resume(t) }
        override fun onError(error: Throwable) { cont.resumeWithException(error) }
    })
}

// ------------------------ SingleSource ------------------------

/**
 * Awaits for completion of the single value without blocking a thread.
 * Returns the resulting value or throws the corresponding exception if this single had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> SingleSource<T>.await(): T = suspendCancellableCoroutine { cont ->
    subscribe(object : SingleObserver<T> {
        override fun onSubscribe(d: Disposable) { cont.disposeOnCancellation(d) }
        override fun onSuccess(t: T) { cont.resume(t) }
        override fun onError(error: Throwable) { cont.resumeWithException(error) }
    })
}

// ------------------------ ObservableSource ------------------------

/**
 * Awaits for the first value from the given observable without blocking a thread.
 * Returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if observable does not emit any value
 */
public suspend fun <T> ObservableSource<T>.awaitFirst(): T = awaitOne(Mode.FIRST)

/**
 * Awaits for the first value from the given observable or the [default] value if none is emitted without blocking a
 * thread and returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> ObservableSource<T>.awaitFirstOrDefault(default: T): T = awaitOne(Mode.FIRST_OR_DEFAULT, default)

/**
 * Awaits for the first value from the given observable or `null` value if none is emitted without blocking a
 * thread and returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> ObservableSource<T>.awaitFirstOrNull(): T? = awaitOne(Mode.FIRST_OR_DEFAULT)

/**
 * Awaits for the first value from the given observable or call [defaultValue] to get a value if none is emitted without blocking a
 * thread and returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> ObservableSource<T>.awaitFirstOrElse(defaultValue: () -> T): T = awaitOne(Mode.FIRST_OR_DEFAULT) ?: defaultValue()

/**
 * Awaits for the last value from the given observable without blocking a thread.
 * Returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if observable does not emit any value
 */
public suspend fun <T> ObservableSource<T>.awaitLast(): T = awaitOne(Mode.LAST)

/**
 * Awaits for the single value from the given observable without blocking a thread.
 * Returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if observable does not emit any value
 * @throws IllegalArgumentException if observable emits more than one value
 */
public suspend fun <T> ObservableSource<T>.awaitSingle(): T = awaitOne(Mode.SINGLE)

// ------------------------ private ------------------------

internal fun CancellableContinuation<*>.disposeOnCancellation(d: Disposable) =
    invokeOnCancellation { d.dispose() }

private enum class Mode(val s: String) {
    FIRST("awaitFirst"),
    FIRST_OR_DEFAULT("awaitFirstOrDefault"),
    LAST("awaitLast"),
    SINGLE("awaitSingle");
    override fun toString(): String = s
}

private suspend fun <T> ObservableSource<T>.awaitOne(
    mode: Mode,
    default: T? = null
): T = suspendCancellableCoroutine { cont ->
    subscribe(object : Observer<T> {
        private lateinit var subscription: Disposable
        private var value: T? = null
        private var seenValue = false

        override fun onSubscribe(sub: Disposable) {
            subscription = sub
            cont.invokeOnCancellation { sub.dispose() }
        }

        override fun onNext(t: T) {
            when (mode) {
                Mode.FIRST, Mode.FIRST_OR_DEFAULT -> {
                    if (!seenValue) {
                        seenValue = true
                        cont.resume(t)
                        subscription.dispose()
                    }
                }
                Mode.LAST, Mode.SINGLE -> {
                    if (mode == Mode.SINGLE && seenValue) {
                        if (cont.isActive)
                            cont.resumeWithException(IllegalArgumentException("More than one onNext value for $mode"))
                        subscription.dispose()
                    } else {
                        value = t
                        seenValue = true
                    }
                }
            }
        }

        @Suppress("UNCHECKED_CAST")
        override fun onComplete() {
            if (seenValue) {
                if (cont.isActive) cont.resume(value as T)
                return
            }
            when {
                mode == Mode.FIRST_OR_DEFAULT -> {
                    cont.resume(default as T)
                }
                cont.isActive -> {
                    cont.resumeWithException(NoSuchElementException("No value received via onNext for $mode"))
                }
            }
        }

        override fun onError(e: Throwable) {
            cont.resumeWithException(e)
        }
    })
}
