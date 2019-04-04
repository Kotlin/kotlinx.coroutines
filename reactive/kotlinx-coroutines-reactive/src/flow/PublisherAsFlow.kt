/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import org.reactivestreams.*

/**
 * Transforms the given reactive [Publisher] into [Flow].
 * Backpressure is controlled by [batchSize] parameter that controls the size of in-flight elements
 * and [Subscription.request] size.
 *
 * If any of the resulting flow transformations fails, subscription is immediately cancelled and all in-flights elements
 * are discarded.
 */
@FlowPreview
@JvmOverloads // For nice Java API
@JvmName("from")
public fun <T : Any> Publisher<T>.asFlow(batchSize: Int = 1): Flow<T> =
    PublisherAsFlow(this, batchSize)

private class PublisherAsFlow<T : Any>(private val publisher: Publisher<T>, private val batchSize: Int) : Flow<T> {

    override suspend fun collect(collector: FlowCollector<in T>) {
        val channel = Channel<T>(batchSize)
        val subscriber = ReactiveSubscriber(channel, batchSize)
        publisher.subscribe(subscriber)
        try {
            var consumed = 0
            for (i in channel) {
                collector.emit(i)
                if (++consumed == batchSize) {
                    consumed = 0
                    subscriber.subscription.request(batchSize.toLong())
                }
            }
        } finally {
            subscriber.subscription.cancel()
        }
    }

    @Suppress("SubscriberImplementation")
    private class ReactiveSubscriber<T : Any>(
        private val channel: Channel<T>,
        private val batchSize: Int
    ) : Subscriber<T> {

        lateinit var subscription: Subscription

        override fun onComplete() {
            channel.close()
        }

        override fun onSubscribe(s: Subscription) {
            subscription = s
            s.request(batchSize.toLong())
        }

        override fun onNext(t: T) {
            // Controlled by batch-size
            require(channel.offer(t)) { "Element $t was not added to channel because it was full, $channel" }
        }

        override fun onError(t: Throwable?) {
            channel.close(t)
        }
    }
}
