/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.disposables.Disposable
import kotlinx.coroutines.CancellableContinuation
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.Job
import kotlinx.coroutines.suspendCancellableCoroutine
import kotlin.coroutines.*

// ------------------------ CompletableSource ------------------------

/**
 * Awaits for completion of this completable without blocking the thread.
 * Returns `Unit`, or throws the corresponding exception if this completable produces an error.
 *
 * This suspending function is cancellable. If the [Job] of the invoking coroutine is cancelled or completed while this
 * suspending function is suspended, this function immediately resumes with [CancellationException] and disposes of its
 * subscription.
 */
public suspend fun CompletableSource.await(): Unit = suspendCancellableCoroutine { cont ->
    subscribe(object : CompletableObserver {
        override fun onSubscribe(d: Disposable) {
            cont.disposeOnCancellation(d)
        }

        override fun onComplete() {
            cont.resume(Unit)
        }

        override fun onError(e: Throwable) {
            cont.resumeWithException(e)
        }
    })
}

// ------------------------ MaybeSource ------------------------

/**
 * Awaits for completion of the [MaybeSource] without blocking the thread.
 * Returns the resulting value, or `null` if no value is produced, or throws the corresponding exception if this
 * [MaybeSource] produces an error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this
 * function immediately resumes with [CancellationException] and disposes of its subscription.
 */
public suspend fun <T> MaybeSource<T>.awaitSingleOrNull(): T? = suspendCancellableCoroutine { cont ->
    subscribe(object : MaybeObserver<T> {
        override fun onSubscribe(d: Disposable) {
            cont.disposeOnCancellation(d)
        }

        override fun onComplete() {
            cont.resume(null)
        }

        override fun onSuccess(t: T & Any) {
            cont.resume(t)
        }

        override fun onError(error: Throwable) {
            cont.resumeWithException(error)
        }
    })
}

/**
 * Awaits for completion of the [MaybeSource] without blocking the thread.
 * Returns the resulting value, or throws if either no value is produced or this [MaybeSource] produces an error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this
 * function immediately resumes with [CancellationException] and disposes of its subscription.
 *
 * @throws NoSuchElementException if no elements were produced by this [MaybeSource].
 */
public suspend fun <T> MaybeSource<T>.awaitSingle(): T = awaitSingleOrNull() ?: throw NoSuchElementException()

/**
 * Awaits for completion of the maybe without blocking a thread.
 * Returns the resulting value, null if no value was produced or throws the corresponding exception if this
 * maybe had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * ### Deprecation
 *
 * Deprecated in favor of [awaitSingleOrNull] in order to reflect that `null` can be returned to denote the absence of
 * a value, as opposed to throwing in such case.
 * @suppress
 */
@Deprecated(
    message = "Deprecated in favor of awaitSingleOrNull()",
    level = DeprecationLevel.ERROR,
    replaceWith = ReplaceWith("this.awaitSingleOrNull()")
) // Warning since 1.5, error in 1.6, hidden in 1.7
public suspend fun <T> MaybeSource<T>.await(): T? = awaitSingleOrNull()

/**
 * Awaits for completion of the maybe without blocking a thread.
 * Returns the resulting value, [default] if no value was produced or throws the corresponding exception if this
 * maybe had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * ### Deprecation
 *
 * Deprecated in favor of [awaitSingleOrNull] for naming consistency (see the deprecation of [MaybeSource.await] for
 * details).
 * @suppress
 */
@Deprecated(
    message = "Deprecated in favor of awaitSingleOrNull()",
    level = DeprecationLevel.ERROR,
    replaceWith = ReplaceWith("this.awaitSingleOrNull() ?: default")
) // Warning since 1.5, error in 1.6, hidden in 1.7
public suspend fun <T> MaybeSource<T>.awaitOrDefault(default: T): T = awaitSingleOrNull() ?: default

// ------------------------ SingleSource ------------------------

/**
 * Awaits for completion of the single value response without blocking the thread.
 * Returns the resulting value, or throws the corresponding exception if this response produces an error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately disposes of its subscription and resumes with [CancellationException].
 */
public suspend fun <T> SingleSource<T>.await(): T = suspendCancellableCoroutine { cont ->
    subscribe(object : SingleObserver<T> {
        override fun onSubscribe(d: Disposable) {
            cont.disposeOnCancellation(d)
        }

        override fun onSuccess(t: T & Any) {
            cont.resume(t)
        }

        override fun onError(error: Throwable) {
            cont.resumeWithException(error)
        }
    })
}

// ------------------------ ObservableSource ------------------------

/**
 * Awaits the first value from the given [Observable] without blocking the thread and returns the resulting value, or,
 * if the observable has produced an error, throws the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately disposes of its subscription and resumes with [CancellationException].
 *
 * @throws NoSuchElementException if the observable does not emit any value
 */
public suspend fun <T> ObservableSource<T>.awaitFirst(): T = awaitOne(Mode.FIRST)

/**
 * Awaits the first value from the given [Observable], or returns the [default] value if none is emitted, without
 * blocking the thread, and returns the resulting value, or, if this observable has produced an error, throws the
 * corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately disposes of its subscription and resumes with [CancellationException].
 */
public suspend fun <T> ObservableSource<T>.awaitFirstOrDefault(default: T): T = awaitOne(Mode.FIRST_OR_DEFAULT, default)

/**
 * Awaits the first value from the given [Observable], or returns `null` if none is emitted, without blocking the
 * thread, and returns the resulting value, or, if this observable has produced an error, throws the corresponding
 * exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately disposes of its subscription and resumes with [CancellationException].
 */
public suspend fun <T> ObservableSource<T>.awaitFirstOrNull(): T? = awaitOne(Mode.FIRST_OR_DEFAULT)

/**
 * Awaits the first value from the given [Observable], or calls [defaultValue] to get a value if none is emitted,
 * without blocking the thread, and returns the resulting value, or, if this observable has produced an error, throws
 * the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately disposes of its subscription and resumes with [CancellationException].
 */
public suspend fun <T> ObservableSource<T>.awaitFirstOrElse(defaultValue: () -> T): T =
    awaitOne(Mode.FIRST_OR_DEFAULT) ?: defaultValue()

/**
 * Awaits the last value from the given [Observable] without blocking the thread and
 * returns the resulting value, or, if this observable has produced an error, throws the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately disposes of its subscription and resumes with [CancellationException].
 *
 * @throws NoSuchElementException if the observable does not emit any value
 */
public suspend fun <T> ObservableSource<T>.awaitLast(): T = awaitOne(Mode.LAST)

/**
 * Awaits the single value from the given observable without blocking the thread and returns the resulting value, or,
 * if this observable has produced an error, throws the corresponding exception.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while the suspending function is waiting, this
 * function immediately disposes of its subscription and resumes with [CancellationException].
 *
 * @throws NoSuchElementException if the observable does not emit any value
 * @throws IllegalArgumentException if the observable emits more than one value
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

        override fun onNext(t: T & Any) {
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

