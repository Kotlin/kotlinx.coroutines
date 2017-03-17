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

import kotlinx.coroutines.experimental.channels.LinkedListChannel
import kotlinx.coroutines.experimental.channels.ReceiveChannel
import org.reactivestreams.Publisher
import org.reactivestreams.Subscriber
import org.reactivestreams.Subscription
import java.io.Closeable
import java.util.concurrent.atomic.AtomicIntegerFieldUpdater

/**
 * Return type for [Publisher.open] that can be used to [receive] elements from the
 * subscription and to manually [close] it.
 */
public interface SubscriptionReceiveChannel<out T> : ReceiveChannel<T>, Closeable {
    /**
     * Closes this subscription channel.
     */
    public override fun close()
}

/**
 * Subscribes to this [Publisher] and returns a channel to receive elements emitted by it.
 */
public fun <T> Publisher<T>.open(): SubscriptionReceiveChannel<T> {
    val channel = SubscriptionChannel<T>()
    subscribe(channel)
    return channel
}

/**
 * Subscribes to this [Publisher] and returns an iterator to receive elements emitted by it.
 *
 * This is a shortcut for `open().iterator()`. See [open] if you need an ability to manually
 * unsubscribe from the observable.
 */

@Suppress("DeprecatedCallableAddReplaceWith")
@Deprecated(message =
    "This iteration operator for `for (x in source) { ... }` loop is deprecated, " +
    "because it leaves code vulnerable to leaving unclosed subscriptions on exception. " +
    "Use `source.consumeEach { x -> ... }`.")
public operator fun <T> Publisher<T>.iterator() = open().iterator()

/**
 * Subscribes to this [Publisher] and performs the specified action for each received element.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <T> Publisher<T>.consumeEach(action: suspend (T) -> Unit) {
    open().use { channel ->
        for (x in channel) action(x)
    }
}

private class SubscriptionChannel<T> : LinkedListChannel<T>(), SubscriptionReceiveChannel<T>, Subscriber<T> {
    @Volatile
    @JvmField
    var subscription: Subscription? = null

    @Volatile
    @JvmField
    // request balance from cancelled receivers, balance is negative if we have receivers, but no subscription yet
    var balance = 0

    private companion object {
        @JvmField
        val BALANCE: AtomicIntegerFieldUpdater<SubscriptionChannel<*>> =
            AtomicIntegerFieldUpdater.newUpdater(SubscriptionChannel::class.java, "balance")
    }

    // AbstractChannel overrides
    override fun onEnqueuedReceive() {
        loop@ while (true) { // lock-free loop on balance
            val balance = this.balance
            val subscription = this.subscription
            if (subscription != null) {
                if (balance < 0) { // receivers came before we had subscription
                    // try to fixup by making request
                    if (!BALANCE.compareAndSet(this, balance, 0)) continue@loop
                    subscription.request(-balance.toLong())
                    return
                }
                if (balance == 0) { // normal story
                    subscription.request(1)
                    return
                }
            }
            if (BALANCE.compareAndSet(this, balance, balance - 1)) return
        }
    }

    override fun onCancelledReceive() {
        BALANCE.incrementAndGet(this)
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
            val balance = this.balance
            if (balance >= 0) return // ok -- normal story
            // otherwise, receivers came before we had subscription
            // try to fixup by making request
            if (!BALANCE.compareAndSet(this, balance, 0)) continue
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

