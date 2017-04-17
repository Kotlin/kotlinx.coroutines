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

import kotlinx.coroutines.experimental.channels.LinkedListChannel
import kotlinx.coroutines.experimental.channels.SubscriptionReceiveChannel
import rx.Observable
import rx.Subscriber
import rx.Subscription
import java.util.concurrent.atomic.AtomicIntegerFieldUpdater

/**
 * Subscribes to this [Observable] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [closed][SubscriptionReceiveChannel.close] to unsubscribe from this observable.
 */
public fun <T> Observable<T>.open(): SubscriptionReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    val subscription = subscribe(channel.subscriber)
    channel.subscription = subscription
    if (channel.isClosedForSend) subscription.unsubscribe()
    return channel
}

/**
 * Subscribes to this [Observable] and returns an iterator to receive elements emitted by it.
 *
 * This is a shortcut for `open().iterator()`. See [open] if you need an ability to manually
 * unsubscribe from the observable.
 */
@Suppress("DeprecatedCallableAddReplaceWith")
@Deprecated(message =
"This iteration operator for `for (x in source) { ... }` loop is deprecated, " +
    "because it leaves code vulnerable to leaving unclosed subscriptions on exception. " +
    "Use `source.consumeEach { x -> ... }`.")
public operator fun <T> Observable<T>.iterator() = open().iterator()

/**
 * Subscribes to this [Observable] and performs the specified action for each received element.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> Observable<T>.consumeEach(action: suspend (T) -> Unit) {
    open().use { channel ->
        for (x in channel) action(x)
    }
}

private class SubscriptionChannel<T> : LinkedListChannel<T>(), SubscriptionReceiveChannel<T> {
    @JvmField
    val subscriber: ChannelSubscriber = ChannelSubscriber()

    @Volatile
    @JvmField
    var subscription: Subscription? = null

    @Volatile
    @JvmField
    var balance = 0 // request balance from cancelled receivers

    private companion object {
        @JvmField
        val BALANCE: AtomicIntegerFieldUpdater<SubscriptionChannel<*>> =
            AtomicIntegerFieldUpdater.newUpdater(SubscriptionChannel::class.java, "balance")
    }

    // AbstractChannel overrides
    override fun onEnqueuedReceive() {
        while (true) { // lock-free loop on balance
            val balance = this.balance
            if (balance == 0) {
                subscriber.requestOne()
                return
            }
            if (BALANCE.compareAndSet(this, balance, balance - 1)) return
        }
    }

    override fun onCancelledReceive() {
        BALANCE.incrementAndGet(this)
    }

    override fun afterClose(cause: Throwable?) {
        subscription?.unsubscribe()
    }

    // Subscription overrides
    override fun close() {
        close(cause = null)
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
