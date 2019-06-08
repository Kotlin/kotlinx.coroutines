/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.flow.*
import org.reactivestreams.*
import kotlin.coroutines.*

/**
 * Converts this job to the hot reactive completable that signals
 * with [onCompleted][CompletableSubscriber.onCompleted] when the corresponding job completes.
 *
 * Every subscriber gets the signal at the same time.
 * Unsubscribing from the resulting completable **does not** affect the original job in any way.
 *
 * **Note: This is an experimental api.** Conversion of coroutines primitives to reactive entities may change
 *    in the future to account for the concept of structured concurrency.
 *
 * @param context -- the coroutine context from which the resulting completable is going to be signalled
 */
@ExperimentalCoroutinesApi
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
 * **Note: This is an experimental api.** Conversion of coroutines primitives to reactive entities may change
 *    in the future to account for the concept of structured concurrency.
 *
 * @param context -- the coroutine context from which the resulting maybe is going to be signalled
 */
@ExperimentalCoroutinesApi
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
 * **Note: This is an experimental api.** Conversion of coroutines primitives to reactive entities may change
 *    in the future to account for the concept of structured concurrency.
 *
 * @param context -- the coroutine context from which the resulting single is going to be signalled
 */
@ExperimentalCoroutinesApi
public fun <T : Any> Deferred<T>.asSingle(context: CoroutineContext): Single<T> = GlobalScope.rxSingle(context) {
    this@asSingle.await()
}

/**
 * Converts a stream of elements received from the channel to the hot reactive observable.
 *
 * Every subscriber receives values from this channel in **fan-out** fashion. If the are multiple subscribers,
 * they'll receive values in round-robin way.
 *
 * **Note: This API will become obsolete in future updates with introduction of lazy asynchronous streams.**
 *           See [issue #254](https://github.com/Kotlin/kotlinx.coroutines/issues/254).
 *
 * @param context -- the coroutine context from which the resulting observable is going to be signalled
 */
@ObsoleteCoroutinesApi
public fun <T : Any> ReceiveChannel<T>.asObservable(context: CoroutineContext): Observable<T> = GlobalScope.rxObservable(context) {
    for (t in this@asObservable)
        send(t)
}

/**
 * Converts the given flow to a cold observable.
 * The original flow is cancelled if the observable subscriber was disposed.
 */
@JvmName("from")
@ExperimentalCoroutinesApi
public fun <T: Any> Flow<T>.asObservable() : Observable<T> = Observable.create { emitter ->
    /*
     * ATOMIC is used here to provide stable behaviour of subscribe+dispose pair even if
     * asObservable is already invoked from unconfined
     */
    val job = GlobalScope.launch(Dispatchers.Unconfined, start = CoroutineStart.ATOMIC) {
        try {
            collect { value -> emitter.onNext(value) }
            emitter.onComplete()
        } catch (e: Throwable) {
            // 'create' provides safe emitter, so we can unconditionally call on* here if exception occurs in `onComplete`
            if (e !is CancellationException) emitter.onError(e)
            else emitter.onComplete()

        }
    }
    emitter.setCancellable(RxCancellable(job))
}

/**
 * Converts the given flow to a cold observable.
 * The original flow is cancelled if the flowable subscriber was disposed.
 */
@JvmName("from")
@ExperimentalCoroutinesApi
public fun <T: Any> Flow<T>.asFlowable(): Flowable<T> = Flowable.fromPublisher(asPublisher())
