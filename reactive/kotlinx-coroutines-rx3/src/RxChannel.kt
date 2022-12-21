/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import io.reactivex.rxjava3.core.*
import io.reactivex.rxjava3.disposables.*
import kotlinx.atomicfu.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*

/**
 * Subscribes to this [MaybeSource] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this source.
 *
 * This API is internal in the favour of [Flow].
 * [MaybeSource] doesn't have a corresponding [Flow] adapter, so it should be transformed to [Observable] first.
 */
@PublishedApi
internal fun <T> MaybeSource<T & Any>.openSubscription(): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

/**
 * Subscribes to this [ObservableSource] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this source.
 *
 * This API is internal in the favour of [Flow].
 * [ObservableSource] doesn't have a corresponding [Flow] adapter, so it should be transformed to [Observable] first.
 */
@PublishedApi
internal fun <T> ObservableSource<T & Any>.openSubscription(): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

/**
 * Subscribes to this [MaybeSource] and performs the specified action for each received element.
 *
 * If [action] throws an exception at some point or if the [MaybeSource] raises an error, the exception is rethrown from
 * [collect].
 */
public suspend inline fun <T> MaybeSource<T & Any>.collect(action: (T) -> Unit): Unit =
    openSubscription().consumeEach(action)

/**
 * Subscribes to this [ObservableSource] and performs the specified action for each received element.
 *
 * If [action] throws an exception at some point, the subscription is cancelled, and the exception is rethrown from
 * [collect]. Also, if the [ObservableSource] signals an error, that error is rethrown from [collect].
 */
public suspend inline fun <T> ObservableSource<T & Any>.collect(action: (T) -> Unit): Unit = openSubscription().consumeEach(action)

@Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
private class SubscriptionChannel<T> :
    BufferedChannel<T>(capacity = Channel.UNLIMITED), Observer<T & Any>, MaybeObserver<T & Any>
{
    private val _subscription = atomic<Disposable?>(null)

    @Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER")
    override fun onClosedIdempotent() {
        _subscription.getAndSet(null)?.dispose() // dispose exactly once
    }

    // Observer overrider
    override fun onSubscribe(sub: Disposable) {
        _subscription.value = sub
    }

    override fun onSuccess(t: T & Any) {
        trySend(t)
        close(cause = null)
    }

    override fun onNext(t: T & Any) {
        trySend(t) // Safe to ignore return value here, expectedly racing with cancellation
    }

    override fun onComplete() {
        close(cause = null)
    }

    override fun onError(e: Throwable) {
        close(cause = e)
    }
}
