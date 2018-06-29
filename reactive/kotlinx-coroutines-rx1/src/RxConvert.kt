/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx1

import kotlinx.coroutines.experimental.Deferred
import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.channels.ReceiveChannel
import rx.*
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
