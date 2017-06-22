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

import io.reactivex.*
import io.reactivex.disposables.Disposable
import kotlinx.coroutines.experimental.channels.LinkedListChannel
import kotlinx.coroutines.experimental.channels.SubscriptionReceiveChannel

/**
 * Subscribes to this [MaybeSource] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [closed][SubscriptionReceiveChannel.close] to unsubscribe from this source.
 */
public fun <T> MaybeSource<T>.openSubscription(): SubscriptionReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

/**
 * @suppress **Deprecated**: Renamed to [openSubscription]
 */
@Deprecated(message = "Renamed to `openSubscription`",
    replaceWith = ReplaceWith("openSubscription()"))
public fun <T> MaybeSource<T>.open(): SubscriptionReceiveChannel<T> = openSubscription()

/**
 * Subscribes to this [ObservableSource] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [closed][SubscriptionReceiveChannel.close] to unsubscribe from this source.
 */
public fun <T> ObservableSource<T>.openSubscription(): SubscriptionReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

/**
 * @suppress **Deprecated**: Renamed to [openSubscription]
 */
@Deprecated(message = "Renamed to `openSubscription`",
    replaceWith = ReplaceWith("openSubscription()"))
public fun <T> ObservableSource<T>.open(): SubscriptionReceiveChannel<T> = openSubscription()

/**
 * Subscribes to this [Observable] and returns an iterator to receive elements emitted by it.
 *
 * This is a shortcut for `open().iterator()`. See [openSubscription] if you need an ability to manually
 * unsubscribe from the observable.
 */
@Suppress("DeprecatedCallableAddReplaceWith")
@Deprecated(message =
"This iteration operator for `for (x in source) { ... }` loop is deprecated, " +
    "because it leaves code vulnerable to leaving unclosed subscriptions on exception. " +
    "Use `source.consumeEach { x -> ... }`.")
public operator fun <T> ObservableSource<T>.iterator() = openSubscription().iterator()

/**
 * Subscribes to this [MaybeSource] and performs the specified action for each received element.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> MaybeSource<T>.consumeEach(action: suspend (T) -> Unit) {
    openSubscription().use { channel ->
        for (x in channel) action(x)
    }
}

/**
 * Subscribes to this [ObservableSource] and performs the specified action for each received element.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> ObservableSource<T>.consumeEach(action: suspend (T) -> Unit) {
    openSubscription().use { channel ->
        for (x in channel) action(x)
    }
}

private class SubscriptionChannel<T> : LinkedListChannel<T>(), SubscriptionReceiveChannel<T>, Observer<T>, MaybeObserver<T> {
    @Volatile
    var subscription: Disposable? = null

    // AbstractChannel overrides
    override fun afterClose(cause: Throwable?) {
        subscription?.dispose()
    }

    // Subscription overrides
    override fun close() {
        close(cause = null)
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
