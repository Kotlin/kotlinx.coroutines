/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.internal.*
import org.reactivestreams.*

/**
 * Subscribes to this [Publisher] and returns a channel to receive elements emitted by it.
 * The resulting channel shall be [cancelled][ReceiveChannel.cancel] to unsubscribe from this publisher.
 *
 * **Note: This API will become obsolete in future updates with introduction of lazy asynchronous streams.**
 *           See [issue #254](https://github.com/Kotlin/kotlinx.coroutines/issues/254).
 *
 * @param request how many items to request from publisher in advance (optional, on-demand request by default).
 */
@ObsoleteCoroutinesApi
@Suppress("CONFLICTING_OVERLOADS")
public fun <T> Publisher<T>.openSubscription(request: Int = 0): ReceiveChannel<T> {
    val channel = SubscriptionChannel<T>(request)
    subscribe(channel)
    return channel
}

/**
 * Subscribes to this [Publisher] and performs the specified action for each received element.
 */
public suspend inline fun <T> Publisher<T>.consumeEach(action: (T) -> Unit) {
    openSubscription().consumeEach(action)
}

@Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
private class SubscriptionChannel<T>(
    private val request: Int
) : LinkedListChannel<T>(), Subscriber<T> {
    init {
        require(request >= 0) { "Invalid request size: $request" }
    }

    @Volatile
    private var subscription: Subscription? = null

    // requested from subscription minus number of received minus number of enqueued receivers,
    // can be negative if we have receivers, but no subscription yet
    private val _requested = atomic(0)

    // AbstractChannel overrides
    @Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER")
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

    @Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER")
    override fun onReceiveDequeued() {
        _requested.incrementAndGet()
    }

    @Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER")
    override fun onClosedIdempotent(closed: LockFreeLinkedListNode) {
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

