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

package kotlinx.coroutines.experimental.rx1

import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.loop
import kotlinx.coroutines.experimental.channels.LinkedListChannel
import kotlinx.coroutines.experimental.channels.SubscriptionReceiveChannel
import rx.Observable
import rx.Subscriber
import rx.Subscription

/**
 * Subscribes to this [Observable] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [closed][SubscriptionReceiveChannel.close] to unsubscribe from this observable.
 */
public fun <T> Observable<T>.openSubscription(): SubscriptionReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    val subscription = subscribe(channel.subscriber)
    channel.subscription = subscription
    if (channel.isClosedForSend) subscription.unsubscribe()
    return channel
}

/**
 * @suppress **Deprecated**: Renamed to [openSubscription]
 */
@Deprecated(message = "Renamed to `openSubscription`",
    replaceWith = ReplaceWith("openSubscription()"))
public fun <T> Observable<T>.open(): SubscriptionReceiveChannel<T> = openSubscription()

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
public operator fun <T> Observable<T>.iterator() = openSubscription().iterator()

/**
 * Subscribes to this [Observable] and performs the specified action for each received element.
 */
public inline suspend fun <T> Observable<T>.consumeEach(action: (T) -> Unit) {
    openSubscription().use { channel ->
        for (x in channel) action(x)
    }
}

/**
 * @suppress: **Deprecated**: binary compatibility with old code
 */
@Deprecated("binary compatibility with old code", level = DeprecationLevel.HIDDEN)
public suspend fun <T> Observable<T>.consumeEach(action: suspend (T) -> Unit) =
    consumeEach { action(it) }

private class SubscriptionChannel<T> : LinkedListChannel<T>(), SubscriptionReceiveChannel<T> {
    @JvmField
    val subscriber: ChannelSubscriber = ChannelSubscriber()

    @Volatile
    @JvmField
    var subscription: Subscription? = null

    val _balance = atomic(0) // request balance from cancelled receivers

    // AbstractChannel overrides
    override fun onEnqueuedReceive() {
        _balance.loop { balance ->
            if (balance == 0) {
                subscriber.requestOne()
                return
            }
            if (_balance.compareAndSet(balance, balance - 1)) return
        }
    }

    override fun onCancelledReceive() {
        _balance.incrementAndGet()
    }

    override fun afterClose(cause: Throwable?) {
        subscription?.unsubscribe()
    }

    inner class ChannelSubscriber: Subscriber<T>() {
        fun requestOne() {
            request(1)
        }

        override fun onStart() {
            request(0) // init backpressure, but don't request anything yet
        }

        override fun onNext(t: T) {
            offer(t)
        }

        override fun onCompleted() {
            close(cause = null)
        }

        override fun onError(e: Throwable) {
            close(cause = e)
        }
    }
}
