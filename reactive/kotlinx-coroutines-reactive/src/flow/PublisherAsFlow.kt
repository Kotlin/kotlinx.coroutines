/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.flow.internal.*
import org.reactivestreams.*
import kotlin.coroutines.*

/**
 * Transforms the given reactive [Publisher] into [Flow].
 * Use [buffer] operator on the resulting flow to specify the size of the backpressure.
 * More precisely, to it specifies the value of the subscription's [request][Subscription.request].
 * `1` is used by default.
 *
 * If any of the resulting flow transformations fails, subscription is immediately cancelled and all in-flights elements
 * are discarded.
 */
@JvmName("from")
@ExperimentalCoroutinesApi
public fun <T : Any> Publisher<T>.asFlow(): Flow<T> =
    PublisherAsFlow(this, 1)

@FlowPreview
@JvmName("from")
@Deprecated(
    message = "batchSize parameter is deprecated, use .buffer() instead to control the backpressure",
    level = DeprecationLevel.ERROR,
    replaceWith = ReplaceWith("asFlow().buffer(batchSize)", imports = ["kotlinx.coroutines.flow.*"])
)
public fun <T : Any> Publisher<T>.asFlow(batchSize: Int): Flow<T> = asFlow().buffer(batchSize)


private class PublisherAsFlow<T : Any>(
    private val publisher: Publisher<T>, capacity: Int
) : ChannelFlow<T>(
    EmptyCoroutineContext,
    capacity
) {

    override fun create(context: CoroutineContext, capacity: Int): ChannelFlow<T> {
        return PublisherAsFlow(publisher, capacity)
    }

    /*
     * It's possible to get rid of the second channel here, but it requires intrusive changes in ChannelFlow.
     * Do it after API stabilization (including produceIn/broadcastIn).
     */
    override suspend fun collectTo(scope: ProducerScope<T>) = collect { scope.send(it) }

    override suspend fun collect(collector: FlowCollector<T>) {
        val channel = Channel<T>(capacity)
        val subscriber = ReactiveSubscriber(channel, capacity)
        publisher.subscribe(subscriber)
        try {
            var consumed = 0
            for (i in channel) {
                collector.emit(i)
                if (++consumed == capacity) {
                    consumed = 0
                    subscriber.subscription.request(capacity.toLong())
                }
            }
        } finally {
            subscriber.subscription.cancel()
        }
    }

    private suspend inline fun collect(emit: (element: T) -> Unit) {
        val channel = Channel<T>(capacity)
        val subscriber = ReactiveSubscriber(channel, capacity)
        publisher.subscribe(subscriber)
        try {
            var consumed = 0
            for (i in channel) {
                emit(i)
                if (++consumed == capacity) {
                    consumed = 0
                    subscriber.subscription.request(capacity.toLong())
                }
            }
        } finally {
            subscriber.subscription.cancel()
        }
    }
}

@Suppress("SubscriberImplementation")
private class ReactiveSubscriber<T : Any>(
    private val channel: Channel<T>,
    private val requestSize: Int
) : Subscriber<T> {

    lateinit var subscription: Subscription

    override fun onComplete() {
        channel.close()
    }

    override fun onSubscribe(s: Subscription) {
        subscription = s
        s.request(requestSize.toLong())
    }

    override fun onNext(t: T) {
        // Controlled by requestSize
        require(channel.offer(t)) { "Element $t was not added to channel because it was full, $channel" }
    }

    override fun onError(t: Throwable?) {
        channel.close(t)
    }
}
