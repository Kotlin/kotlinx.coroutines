/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.*
import io.reactivex.disposables.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*

/**
 * Subscribes to this [MaybeSource] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this source.
 *
 * **Note: This API will become obsolete in future updates with introduction of lazy asynchronous streams.**
 *           See [issue #254](https://github.com/Kotlin/kotlinx.coroutines/issues/254).
 */
@ObsoleteCoroutinesApi
@Suppress("CONFLICTING_OVERLOADS")
public fun <T> MaybeSource<T>.openSubscription(): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

/** @suppress **Deprecated**: Left here for binary compatibility */
@Deprecated(level = DeprecationLevel.HIDDEN, message = "Left here for binary compatibility")
@Suppress("CONFLICTING_OVERLOADS")
public fun <T> MaybeSource<T>.openSubscription(): SubscriptionReceiveChannel<T> =
    openSubscription() as SubscriptionReceiveChannel<T>
/**
 * Subscribes to this [ObservableSource] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this source.
 *
 * **Note: This API will become obsolete in future updates with introduction of lazy asynchronous streams.**
 *           See [issue #254](https://github.com/Kotlin/kotlinx.coroutines/issues/254).
 */
@ObsoleteCoroutinesApi
@Suppress("CONFLICTING_OVERLOADS")
public fun <T> ObservableSource<T>.openSubscription(): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

/** @suppress **Deprecated**: Left here for binary compatibility */
@Deprecated(level = DeprecationLevel.HIDDEN, message = "Left here for binary compatibility")
@Suppress("CONFLICTING_OVERLOADS")
public fun <T> ObservableSource<T>.openSubscription(): SubscriptionReceiveChannel<T> =
    openSubscription() as SubscriptionReceiveChannel<T>

/**
 * Subscribes to this [MaybeSource] and performs the specified action for each received element.
 */
public suspend inline fun <T> MaybeSource<T>.consumeEach(action: (T) -> Unit) {
    val channel = openSubscription()
    for (x in channel) action(x)
    channel.cancel()
}

/**
 * Subscribes to this [ObservableSource] and performs the specified action for each received element.
 */
public suspend inline fun <T> ObservableSource<T>.consumeEach(action: (T) -> Unit) {
    val channel = openSubscription()
    for (x in channel) action(x)
    channel.cancel()
}

private class SubscriptionChannel<T> :
    LinkedListChannel<T>(), ReceiveChannel<T>, Observer<T>, MaybeObserver<T>, SubscriptionReceiveChannel<T>
{
    @Volatile
    var subscription: Disposable? = null

    // AbstractChannel overrides
    override fun afterClose(cause: Throwable?) {
        subscription?.dispose()
    }

    // Observer overrider
    override fun onSubscribe(sub: Disposable) {
        subscription = sub
    }

    override fun onSuccess(t: T) {
        offer(t)
    }

    override fun onNext(t: T) {
        offer(t)
    }

    override fun onComplete() {
        close(cause = null)
    }

    override fun onError(e: Throwable) {
        close(cause = e)
    }
}
