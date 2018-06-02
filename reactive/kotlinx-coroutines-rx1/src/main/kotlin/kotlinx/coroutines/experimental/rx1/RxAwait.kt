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

package kotlinx.coroutines.experimental.rx1

import kotlinx.coroutines.experimental.CancellableContinuation
import kotlinx.coroutines.experimental.CancellationException
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.suspendCancellableCoroutine
import rx.*

// ------------------------ Completable ------------------------

/**
 * Awaits for completion of this completable without blocking a thread.
 * Returns `Unit` or throws the corresponding exception if this completable had produced error.
 *
 * This suspending function is cancellable. If the [Job] of the invoking coroutine is cancelled or completed while this
 * suspending function is suspended, this function immediately resumes with [CancellationException].
 */
public suspend fun Completable.awaitCompleted(): Unit = suspendCancellableCoroutine { cont ->
    subscribe(object : CompletableSubscriber {
        override fun onSubscribe(s: Subscription) { cont.unsubscribeOnCancellation(s) }
        override fun onCompleted() { cont.resume(Unit) }
        override fun onError(e: Throwable) { cont.resumeWithException(e) }
    })
}

// ------------------------ Single ------------------------

/**
 * Awaits for completion of the single value without blocking a thread and
 * returns the resulting value or throws the corresponding exception if this single had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> Single<T>.await(): T = suspendCancellableCoroutine { cont ->
    cont.unsubscribeOnCancellation(subscribe(object : SingleSubscriber<T>() {
        override fun onSuccess(t: T) { cont.resume(t) }
        override fun onError(error: Throwable) { cont.resumeWithException(error) }
    }))
}

// ------------------------ Observable ------------------------

/**
 * Awaits for the first value from the given observable without blocking a thread and
 * returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if observable does not emit any value
 */
public suspend fun <T> Observable<T>.awaitFirst(): T = first().awaitOne()

/**
 * Awaits for the first value from the given observable or the [default] value if none is emitted without blocking a
 * thread and returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> Observable<T>.awaitFirstOrDefault(default: T): T = firstOrDefault(default).awaitOne()

/**
 * Awaits for the first value from the given observable or `null` value if none is emitted without blocking a
 * thread and returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> Observable<T>.awaitFirstOrNull(): T? = firstOrDefault(null).awaitOne()

/**
 * Awaits for the first value from the given observable or call [defaultValue] to get a value if none is emitted without blocking a
 * thread and returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> Observable<T>.awaitFirstOrElse(defaultValue: () -> T): T = switchIfEmpty(Observable.fromCallable(defaultValue)).first().awaitOne()

/**
 * Awaits for the last value from the given observable without blocking a thread and
 * returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if observable does not emit any value
 */
public suspend fun <T> Observable<T>.awaitLast(): T = last().awaitOne()

/**
 * Awaits for the single value from the given observable without blocking a thread and
 * returns the resulting value or throws the corresponding exception if this observable had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if observable does not emit any value
 * @throws IllegalArgumentException if publisher emits more than one value
 */
public suspend fun <T> Observable<T>.awaitSingle(): T = single().awaitOne()

// ------------------------ private ------------------------

private suspend fun <T> Observable<T>.awaitOne(): T = suspendCancellableCoroutine { cont ->
    cont.unsubscribeOnCancellation(subscribe(object : Subscriber<T>() {
        override fun onStart() { request(1) }
        override fun onNext(t: T) { cont.resume(t) }
        override fun onCompleted() { if (cont.isActive) cont.resumeWithException(IllegalStateException("Should have invoked onNext")) }
        override fun onError(e: Throwable) { cont.resumeWithException(e) }
    }))
}

internal fun <T> CancellableContinuation<T>.unsubscribeOnCancellation(sub: Subscription) =
    invokeOnCancellation { sub.unsubscribe() }
