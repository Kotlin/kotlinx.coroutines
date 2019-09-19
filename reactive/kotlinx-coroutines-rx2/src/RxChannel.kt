/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.disposables.*
import kotlinx.atomicfu.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*

/**
 * Subscribes to this [MaybeSource] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this source.
 *
 * This API is deprecated in the favour of [Flow].
 * [MaybeSource] doesn't have a corresponding [Flow] adapter, so it should be transformed to [Observable] first.
 */
@Deprecated(message = "Deprecated in the favour of Flow", level = DeprecationLevel.WARNING) // Will be hidden in 1.4
public fun <T> MaybeSource<T>.openSubscription(): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

/**
 * Subscribes to this [ObservableSource] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this source.
 *
 * This API is deprecated in the favour of [Flow].
 * [ObservableSource] doesn't have a corresponding [Flow] adapter, so it should be transformed to [Observable] first.
 */
@Deprecated(message = "Deprecated in the favour of Flow", level = DeprecationLevel.WARNING) // Will be hidden in 1.4
public fun <T> ObservableSource<T>.openSubscription(): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

// Will be promoted to error in 1.3.0, removed in 1.4.0
@Deprecated(message = "Use collect instead", level = DeprecationLevel.ERROR, replaceWith = ReplaceWith("this.collect(action)"))
public suspend inline fun <T> MaybeSource<T>.consumeEach(action: (T) -> Unit) =
    openSubscription().consumeEach(action)

// Will be promoted to error in 1.3.0, removed in 1.4.0
@Deprecated(message = "Use collect instead", level = DeprecationLevel.ERROR, replaceWith = ReplaceWith("this.collect(action)"))
public suspend inline fun <T> ObservableSource<T>.consumeEach(action: (T) -> Unit) =
    openSubscription().consumeEach(action)

/**
 * Subscribes to this [MaybeSource] and performs the specified action for each received element.
 * Cancels subscription if any exception happens during collect.
 */
public suspend inline fun <T> MaybeSource<T>.collect(action: (T) -> Unit) =
    openSubscription().consumeEach(action)

/**
 * Subscribes to this [ObservableSource] and performs the specified action for each received element.
 * Cancels subscription if any exception happens during collect.
 */
public suspend inline fun <T> ObservableSource<T>.collect(action: (T) -> Unit) =
    openSubscription().consumeEach(action)

@Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
private class SubscriptionChannel<T> :
    LinkedListChannel<T>(), Observer<T>, MaybeObserver<T>
{
    private val _subscription = atomic<Disposable?>(null)

    @Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER")
    override fun onClosedIdempotent(closed: LockFreeLinkedListNode) {
        _subscription.getAndSet(null)?.dispose() // dispose exactly once
    }

    // Observer overrider
    override fun onSubscribe(sub: Disposable) {
        _subscription.value = sub
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
