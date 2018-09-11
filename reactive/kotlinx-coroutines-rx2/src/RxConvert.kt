/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.*

/**
 * Converts this job to the hot reactive completable that signals
 * with [onCompleted][CompletableSubscriber.onCompleted] when the corresponding job completes.
 *
 * Every subscriber gets the signal at the same time.
 * Unsubscribing from the resulting completable **does not** affect the original job in any way.
 *
 * @param context -- the coroutine context from which the resulting completable is going to be signalled
 */
public fun Job.asCompletable(context: CoroutineContext): Completable = GlobalScope.rxCompletable(context) {
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
public fun <T> Deferred<T?>.asMaybe(context: CoroutineContext): Maybe<T> = GlobalScope.rxMaybe(context) {
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
public fun <T> Deferred<T>.asSingle(context: CoroutineContext): Single<T> = GlobalScope.rxSingle(context) {
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
public fun <T> ReceiveChannel<T>.asObservable(context: CoroutineContext): Observable<T> = GlobalScope.rxObservable(context) {
    for (t in this@asObservable)
        send(t)
}
