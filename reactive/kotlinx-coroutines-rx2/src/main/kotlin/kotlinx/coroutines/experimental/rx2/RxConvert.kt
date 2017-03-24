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

import io.reactivex.Completable
import io.reactivex.Maybe
import kotlinx.coroutines.experimental.Deferred
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.channels.ReceiveChannel
import io.reactivex.Observable
import io.reactivex.Single
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Converts this job to the hot reactive completable that signals
 * with [onCompleted][CompletableSubscriber.onCompleted] when the corresponding job completes.
 *
 * Every subscriber gets the signal at the same time.
 * Unsubscribing from the resulting completable **does not** affect the original job in any way.
 *
 * @param context -- the coroutine context from which the resulting completable is going to be signalled
 */
public fun Job.asCompletable(context: CoroutineContext): Completable = rxCompletable(context) {
    this@asCompletable.join()
}

/**
 * Converts this deferred value to the hot reactive maybe that signals
 * [onComplete][MaybeEmitter.onComplete], [onSuccess][MaybeEmitter.onSuccess] or [onError][MaybeEmitter.onError].
 *
 * Every subscriber gets the same completion value.
 * Unsubscribing from the resulting maybe **does not** affect the original deferred value in any way.
 *
 * @param context -- the coroutine context from which the resulting maybe is going to be signalled
 */
public fun <T> Deferred<T?>.asMaybe(context: CoroutineContext): Maybe<T> = rxMaybe<T>(context) {
    this@asMaybe.await()
}

/**
 * Converts this deferred value to the hot reactive single that signals either
 * [onSuccess][SingleSubscriber.onSuccess] or [onError][SingleSubscriber.onError].
 *
 * Every subscriber gets the same completion value.
 * Unsubscribing from the resulting single **does not** affect the original deferred value in any way.
 *
 * @param context -- the coroutine context from which the resulting single is going to be signalled
 */
public fun <T> Deferred<T>.asSingle(context: CoroutineContext): Single<T> = rxSingle<T>(context) {
    this@asSingle.await()
}

/**
 * Converts a stream of elements received from the channel to the hot reactive observable.
 *
 * Every subscriber receives values from this channel in **fan-out** fashion. If the are multiple subscribers,
 * they'll receive values in round-robin way.
 *
 * @param context -- the coroutine context from which the resulting observable is going to be signalled
 */
public fun <T> ReceiveChannel<T>.asObservable(context: CoroutineContext): Observable<T> = rxObservable(context) {
    for (t in this@asObservable)
        send(t)
}

/**
 * @suppress **Deprecated**: Renamed to [asCompletable]
 */
@Deprecated(message = "Renamed to `asCompletable`",
    replaceWith = ReplaceWith("asCompletable(context)"))
public fun Job.toCompletable(context: CoroutineContext): Completable = asCompletable(context)

/**
 * @suppress **Deprecated**: Renamed to [asSingle]
 */
@Deprecated(message = "Renamed to `asSingle`",
    replaceWith = ReplaceWith("asSingle(context)"))
public fun <T> Deferred<T>.toSingle(context: CoroutineContext): Single<T> = asSingle(context)

/**
 * @suppress **Deprecated**: Renamed to [asObservable]
 */
@Deprecated(message = "Renamed to `asObservable`",
    replaceWith = ReplaceWith("asObservable(context)"))
public fun <T> ReceiveChannel<T>.toObservable(context: CoroutineContext): Observable<T> = asObservable(context)
