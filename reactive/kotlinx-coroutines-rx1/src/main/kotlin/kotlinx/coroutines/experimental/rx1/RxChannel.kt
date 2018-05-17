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

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.channels.*
import rx.*

/**
 * Subscribes to this [Observable] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this observable.
 * @param request how many items to request from publisher in advance (optional, on-demand request by default).
 */
@Suppress("CONFLICTING_OVERLOADS")
public fun <T> Observable<T>.openSubscription(request: Int = 0): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>(request)
    val subscription = subscribe(channel.subscriber)
    channel.subscription = subscription
    if (channel.isClosedForSend) subscription.unsubscribe()
    return channel
}

/** @suppress **Deprecated**: Left here for binary compatibility */
@JvmOverloads // for binary compatibility
@Deprecated(level = DeprecationLevel.HIDDEN, message = "Left here for binary compatibility")
@Suppress("CONFLICTING_OVERLOADS")
public fun <T> Observable<T>.openSubscription(request: Int = 0): SubscriptionReceiveChannel<T> =
    openSubscription(request) as SubscriptionReceiveChannel<T>

/**
 * @suppress **Deprecated**: Renamed to [openSubscription]
 */
@Deprecated(message = "Renamed to `openSubscription`",
    replaceWith = ReplaceWith("openSubscription()"))
public fun <T> Observable<T>.open(): SubscriptionReceiveChannel<T> =
    openSubscription() as SubscriptionReceiveChannel<T>

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
public suspend inline fun <T> Observable<T>.consumeEach(action: (T) -> Unit) {
    val channel = openSubscription()
    for (x in channel) action(x)
    channel.cancel()
}

/**
 * @suppress: **Deprecated**: binary compatibility with old code
 */
@Deprecated("binary compatibility with old code", level = DeprecationLevel.HIDDEN)
public suspend fun <T> Observable<T>.consumeEach(action: suspend (T) -> Unit) =
    consumeEach { action(it) }

private class SubscriptionChannel<T>(
    private val request: Int
) : LinkedListChannel<T>(), ReceiveChannel<T>, SubscriptionReceiveChannel<T> {
    init {
        require(request >= 0) { "Invalid request size: $request" }
    }

    @JvmField
    val subscriber: ChannelSubscriber = ChannelSubscriber(request)

    @Volatile
    @JvmField
    var subscription: Subscription? = null

    // requested from subscription minus number of received minus number of enqueued receivers,
    private val _requested = atomic(request)

    // AbstractChannel overrides
    override fun onReceiveEnqueued() {
        _requested.loop { wasRequested ->
            val needRequested = wasRequested - 1
            if (needRequested < 0) { // need to request more from subscriber
                // try to fixup by making request
                if (wasRequested != request && !_requested.compareAndSet(wasRequested, request))
                    return@loop // continue looping if failed
                subscriber.makeRequest((request - needRequested).toLong())
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
        subscription?.unsubscribe()
    }

    inner class ChannelSubscriber(private val request: Int): Subscriber<T>() {
        fun makeRequest(n: Long) {
            request(n)
        }

        override fun onStart() {
            request(request.toLong()) // init backpressure
        }

        override fun onNext(t: T) {
            _requested.decrementAndGet()
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
