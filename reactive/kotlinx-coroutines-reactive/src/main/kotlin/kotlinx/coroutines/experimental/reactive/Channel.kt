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
import kotlinx.coroutines.experimental.channels.ReceiveChannel
import org.reactivestreams.Publisher
import org.reactivestreams.Subscriber
import org.reactivestreams.Subscription

/**
 * Subscribes to this [Publisher] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this publisher.
 * @param request how many items to request from publisher in advance (optional, on-demand request by default).
 */
@JvmOverloads // for binary compatibility
public fun <T> Publisher<T>.openSubscription(request: Int = 0): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>(request)
    subscribe(channel)
    return channel
}

/**
 * @suppress **Deprecated**: Renamed to [openSubscription]
 */
@Deprecated(message = "Renamed to `openSubscription`",
    replaceWith = ReplaceWith("openSubscription()"))
public fun <T> Publisher<T>.open(): ReceiveChannel<T> = openSubscription()

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
public suspend inline fun <T> Publisher<T>.consumeEach(action: (T) -> Unit) {
    val channel = openSubscription()
    for (x in channel) action(x)
    channel.cancel()
}

/**
 * @suppress: **Deprecated**: binary compatibility with old code
 */
@Deprecated("binary compatibility with old code", level = DeprecationLevel.HIDDEN)
public suspend fun <T> Publisher<T>.consumeEach(action: suspend (T) -> Unit) =
    consumeEach { action(it) }

private class SubscriptionChannel<T>(
    private val request: Int
) : LinkedListChannel<T>(), ReceiveChannel<T>, Subscriber<T> {
    init {
        require(request >= 0) { "Invalid request size: $request" }
    }

    @Volatile
    private var subscription: Subscription? = null

    // requested from subscription minus number of received minus number of enqueued receivers,
    // can be negative if we have receivers, but no subscription yet
    private val _requested = atomic(0)

    // AbstractChannel overrides
    override fun onReceiveEnqueued() {
        _requested.loop { wasRequested ->
            val subscription = this.subscription
            val needRequested = wasRequested - 1
            if (subscription != null && needRequested < 0) { // need to request more from subscription
                // try to fixup by making request
                if (wasRequested != request && !_requested.compareAndSet(wasRequested, request))
                    return@loop // continue looping if failed
                subscription.request((request - needRequested).toLong())
                return
            }
            // just do book-keeping
            if (_requested.compareAndSet(wasRequested, needRequested)) return
        }
    }

    override fun onReceiveDequeued() {
        _requested.incrementAndGet()
    }

    override fun afterClose(cause: Throwable?) {
        subscription?.cancel()
    }

    // Subscriber overrides
    override fun onSubscribe(s: Subscription) {
        subscription = s
        while (true) { // lock-free loop on _requested
            if (isClosedForSend) {
                s.cancel()
                return
            }
            val wasRequested = _requested.value
            if (wasRequested >= request) return // ok -- normal story
            // otherwise, receivers came before we had subscription or need to make initial request
            // try to fixup by making request
            if (!_requested.compareAndSet(wasRequested, request)) continue
            s.request((request - wasRequested).toLong())
            return
        }
    }

    override fun onNext(t: T) {
        _requested.decrementAndGet()
        offer(t)
    }

    override fun onComplete() {
        close(cause = null)
    }

    override fun onError(e: Throwable) {
        close(cause = e)
    }
}

