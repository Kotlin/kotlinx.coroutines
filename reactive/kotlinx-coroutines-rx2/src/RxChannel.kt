/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.disposables.*
import kotlinx.atomicfu.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*

/**
 * Subscribes to this [MaybeSource] and performs the specified action for each received element.
 *
 * If [action] throws an exception at some point or if the [MaybeSource] raises an error, the exception is rethrown from
 * [collect].
 */
public suspend inline fun <T> MaybeSource<T>.collect(action: (T) -> Unit): Unit =
    toChannel().consumeEach(action)

/**
 * Subscribes to this [ObservableSource] and performs the specified action for each received element.
 *
 * If [action] throws an exception at some point, the subscription is cancelled, and the exception is rethrown from
 * [collect]. Also, if the [ObservableSource] signals an error, that error is rethrown from [collect].
 */
public suspend inline fun <T> ObservableSource<T>.collect(action: (T) -> Unit): Unit =
    toChannel().consumeEach(action)

@PublishedApi
internal fun <T> MaybeSource<T>.toChannel(): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

@PublishedApi
internal fun <T> ObservableSource<T>.toChannel(): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

@Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
private class SubscriptionChannel<T> :
    BufferedChannel<T>(capacity = Channel.UNLIMITED), Observer<T>, MaybeObserver<T>
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

/** @suppress */
@Deprecated(message = "Deprecated in the favour of Flow", level = DeprecationLevel.HIDDEN) // ERROR in 1.4.0, HIDDEN in 1.6.0
public fun <T> ObservableSource<T & Any>.openSubscription(): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

/** @suppress */
@Deprecated(message = "Deprecated in the favour of Flow", level = DeprecationLevel.HIDDEN) // ERROR in 1.4.0, HIDDEN in 1.6.0
public fun <T> MaybeSource<T & Any>.openSubscription(): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}
