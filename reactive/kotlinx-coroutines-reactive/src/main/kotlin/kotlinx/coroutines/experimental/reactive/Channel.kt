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

package kotlinx.coroutines.experimental.reactive

import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.loop
import kotlinx.coroutines.experimental.channels.LinkedListChannel
import kotlinx.coroutines.experimental.channels.SubscriptionReceiveChannel
import org.reactivestreams.Publisher
import org.reactivestreams.Subscriber
import org.reactivestreams.Subscription

/**
 * Subscribes to this [Publisher] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [closed][SubscriptionReceiveChannel.close] to unsubscribe from this publisher.
 */
public fun <T> Publisher<T>.openSubscription(): SubscriptionReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

/**
 * @suppress **Deprecated**: Renamed to [openSubscription]
 */
@Deprecated(message = "Renamed to `openSubscription`",
    replaceWith = ReplaceWith("openSubscription()"))
public fun <T> Publisher<T>.open(): SubscriptionReceiveChannel<T> = openSubscription()

/**
 * Subscribes to this [Publisher] and returns an iterator to receive elements emitted by it.
 *
 * This is a shortcut for `open().iterator()`. See [openSubscription] if you need an ability to manually
 * unsubscribe from the observable.
 */

@Suppress("DeprecatedCallableAddReplaceWith")
@Deprecated(message =
    "This iteration operator for `for (x in source) { ... }` loop is deprecated, " +
    "because it leaves code vulnerable to leaving unclosed subscriptions on exception. " +
    "Use `source.consumeEach { x -> ... }`.")
public operator fun <T> Publisher<T>.iterator() = openSubscription().iterator()

/**
 * Subscribes to this [Publisher] and performs the specified action for each received element.
 */
public inline suspend fun <T> Publisher<T>.consumeEach(action: (T) -> Unit) {
    openSubscription().use { channel ->
        for (x in channel) action(x)
    }
}

/**
 * @suppress: **Deprecated**: binary compatibility with old code
 */
@Deprecated("binary compatibility with old code", level = DeprecationLevel.HIDDEN)
public suspend fun <T> Publisher<T>.consumeEach(action: suspend (T) -> Unit) =
    consumeEach { action(it) }

private class SubscriptionChannel<T> : LinkedListChannel<T>(), SubscriptionReceiveChannel<T>, Subscriber<T> {
    @Volatile
    @JvmField
    var subscription: Subscription? = null

    // request balance from cancelled receivers, balance is negative if we have receivers, but no subscription yet
    val _balance = atomic(0)

    // AbstractChannel overrides
    override fun onEnqueuedReceive() {
        _balance.loop { balance ->
            val subscription = this.subscription
            if (subscription != null) {
                if (balance < 0) { // receivers came before we had subscription
                    // try to fixup by making request
                    if (!_balance.compareAndSet(balance, 0)) return@loop // continue looping
                    subscription.request(-balance.toLong())
                    return
                }
                if (balance == 0) { // normal story
                    subscription.request(1)
                    return
                }
            }
            if (_balance.compareAndSet(balance, balance - 1)) return
        }
    }

    override fun onCancelledReceive() {
        _balance.incrementAndGet()
    }

    override fun afterClose(cause: Throwable?) {
        subscription?.cancel()
    }

    // Subscription overrides
    override fun close() {
        close(cause = null)
    }

    // Subscriber overrides
    override fun onSubscribe(s: Subscription) {
        subscription = s
        while (true) { // lock-free loop on balance
            if (isClosedForSend) {
                s.cancel()
                return
            }
            val balance = _balance.value
            if (balance >= 0) return // ok -- normal story
            // otherwise, receivers came before we had subscription
            // try to fixup by making request
            if (!_balance.compareAndSet(balance, 0)) continue
            s.request(-balance.toLong())
            return
        }
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

