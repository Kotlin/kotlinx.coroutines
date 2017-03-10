/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.*
import io.reactivex.disposables.Disposable
import kotlinx.coroutines.experimental.CancellableContinuation
import kotlinx.coroutines.experimental.CancellationException
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.suspendCancellableCoroutine

// ------------------------ CompletableSource ------------------------

/**
 * Awaits for completion of this completable without blocking a thread.
 * Returns `Unit` or throws the corresponding exception if this completable had produced error.
 *
 * This suspending function is cancellable. If the [Job] of the invoking coroutine is completed while this
 * suspending function is suspended, this function immediately resumes with [CancellationException].
 */
public suspend fun CompletableSource.await(): Unit = suspendCancellableCoroutine { cont ->
    subscribe(object : CompletableObserver {
        override fun onSubscribe(d: Disposable) { cont.disposeOnCompletion(d) }
        override fun onComplete() { cont.resume(Unit) }
        override fun onError(e: Throwable) { cont.resumeWithException(e) }
    })
}

// ------------------------ SingleSource ------------------------

/**
 * Awaits for completion of the single value without blocking a thread.
 * Returns the resulting value or throws the corresponding exception if this single had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> SingleSource<T>.await(): T = suspendCancellableCoroutine { cont ->
    subscribe(object : SingleObserver<T> {
        override fun onSubscribe(d: Disposable) { cont.disposeOnCompletion(d) }
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
 * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> ObservableSource<T>.awaitFirst(): T = awaitOne(Mode.FIRST)

/**
 * Awaits for the last value from the given observable without blocking a thread.
 * Returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> ObservableSource<T>.awaitLast(): T = awaitOne(Mode.LAST)

/**
 * Awaits for the single value from the given observable without blocking a thread.
 * Returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> ObservableSource<T>.awaitSingle(): T = awaitOne(Mode.SINGLE)

// ------------------------ private ------------------------

internal fun CancellableContinuation<*>.disposeOnCompletion(d: Disposable) =
    invokeOnCompletion { d.dispose() }

private enum class Mode(val s: String) {
    FIRST("awaitFirst"),
    LAST("awaitLast"),
    SINGLE("awaitSingle");
    override fun toString(): String = s
}

private suspend fun <T> ObservableSource<T>.awaitOne(mode: Mode): T = suspendCancellableCoroutine { cont ->
    subscribe(object : Observer<T> {
        private lateinit var subscription: Disposable
        private var value: T? = null
        private var seenValue = false

        override fun onSubscribe(sub: Disposable) {
            subscription = sub
            cont.invokeOnCompletion { sub.dispose() }
        }

        override fun onNext(t: T) {
            when (mode) {
                Mode.FIRST -> {
                    seenValue = true
                    cont.resume(t)
                    subscription.dispose()
                }
                Mode.LAST, Mode.SINGLE -> {
                    if (mode == Mode.SINGLE && seenValue) {
                        if (cont.isActive)
                            cont.resumeWithException(IllegalArgumentException("More that one onNext value for $mode"))
                        subscription.dispose()
                    } else {
                        value = t
                        seenValue = true
                    }
                }
            }
        }

        override fun onComplete() {
            if (!seenValue) {
                if (cont.isActive)
                    cont.resumeWithException(NoSuchElementException("No value received via onNext for $mode"))
                return
            }
            if (!cont.isActive) return // was already resumed
            cont.resume(value as T)
        }

        override fun onError(e: Throwable) {
            cont.resumeWithException(e)
        }
    })
}

