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

package kotlinx.coroutines.experimental.reactive

import kotlinx.coroutines.experimental.CancellationException
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.suspendCancellableCoroutine
import org.reactivestreams.Publisher
import org.reactivestreams.Subscriber
import org.reactivestreams.Subscription

/**
 * Awaits for the first value from the given publisher without blocking a thread and
 * returns the resulting value or throws the corresponding exception if this publisher had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
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
 * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 */
public suspend fun <T> Publisher<T>.awaitFirstOrDefault(default: T): T = awaitOne(Mode.FIRST_OR_DEFAULT, default)

/**
 * Awaits for the last value from the given publisher without blocking a thread and
 * returns the resulting value or throws the corresponding exception if this publisher had produced error.
 *
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
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
 * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException].
 *
 * @throws NoSuchElementException if publisher does not emit any value
 * @throws IllegalArgumentException if publisher emits more than one value
 */
public suspend fun <T> Publisher<T>.awaitSingle(): T = awaitOne(Mode.SINGLE)

// ------------------------ private ------------------------

private enum class Mode(val s: String) {
    FIRST("awaitFirst"),
    FIRST_OR_DEFAULT("awaitFirstOrDefault"),
    LAST("awaitLast"),
    SINGLE("awaitSingle");
    override fun toString(): String = s
}

private suspend fun <T> Publisher<T>.awaitOne(
    mode: Mode,
    default: T? = null
): T = suspendCancellableCoroutine { cont ->
    subscribe(object : Subscriber<T> {
        private lateinit var subscription: Subscription
        private var value: T? = null
        private var seenValue = false

        override fun onSubscribe(sub: Subscription) {
            subscription = sub
            cont.invokeOnCompletion { sub.cancel() }
            sub.request(if (mode == Mode.FIRST) 1 else Long.MAX_VALUE)
        }

        override fun onNext(t: T) {
            when (mode) {
                Mode.FIRST, Mode.FIRST_OR_DEFAULT -> {
                    seenValue = true
                    cont.resume(t)
                    subscription.cancel()
                }
                Mode.LAST, Mode.SINGLE -> {
                    if (mode == Mode.SINGLE && seenValue) {
                        if (cont.isActive)
                            cont.resumeWithException(IllegalArgumentException("More that one onNext value for $mode"))
                        subscription.cancel()
                    } else {
                        value = t
                        seenValue = true
                    }
                }
            }
        }

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

