/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.reactive.*
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
    private val publisher: Publisher<T>,
    capacity: Int
) : ChannelFlow<T>(EmptyCoroutineContext, capacity) {
    override fun create(context: CoroutineContext, capacity: Int): ChannelFlow<T> =
        PublisherAsFlow(publisher, capacity)

    override fun produceImpl(scope: CoroutineScope): ReceiveChannel<T> {
        // use another channel for conflation (cannot do openSubscription)
        if (capacity < 0) return super.produceImpl(scope)
        // Open subscription channel directly
        val channel = publisher.openSubscription(capacity)
        val handle = scope.coroutineContext[Job]?.invokeOnCompletion(onCancelling = true) { cause ->
            channel.cancel(cause?.let {
                it as? CancellationException ?: CancellationException("Job was cancelled", it)
            })
        }
        if (handle != null && handle !== NonDisposableHandle) {
            (channel as SendChannel<*>).invokeOnClose {
                handle.dispose()
            }
        }
        return channel
    }

    private val requestSize: Long
        get() = when (capacity) {
            Channel.CONFLATED -> Long.MAX_VALUE // request all and conflate incoming
            Channel.RENDEZVOUS -> 1L // need to request at least one anyway
            Channel.UNLIMITED -> Long.MAX_VALUE // reactive streams way to say "give all" must be Long.MAX_VALUE
            else -> capacity.toLong().also { check(it >= 1) }
        }

    override suspend fun collect(collector: FlowCollector<T>) {
        val subscriber = ReactiveSubscriber<T>(capacity, requestSize)
        publisher.subscribe(subscriber)
        try {
            var consumed = 0L
            while (true) {
                val value = subscriber.takeNextOrNull() ?: break
                collector.emit(value)
                if (++consumed == requestSize) {
                    consumed = 0L
                    subscriber.makeRequest()
                }
            }
        } finally {
            subscriber.cancel()
        }
    }

    // The second channel here is used only for broadcast
    override suspend fun collectTo(scope: ProducerScope<T>) =
        collect(SendingCollector(scope.channel))
}

@Suppress("SubscriberImplementation")
private class ReactiveSubscriber<T : Any>(
    capacity: Int,
    private val requestSize: Long
) : Subscriber<T> {
    private lateinit var subscription: Subscription
    private val channel = Channel<T>(capacity)

    suspend fun takeNextOrNull(): T? = channel.receiveOrNull()

    override fun onNext(value: T) {
        // Controlled by requestSize
        require(channel.offer(value)) { "Element $value was not added to channel because it was full, $channel" }
    }

    override fun onComplete() {
        channel.close()
    }

    override fun onError(t: Throwable?) {
        channel.close(t)
    }

    override fun onSubscribe(s: Subscription) {
        subscription = s
        makeRequest()
    }

    fun makeRequest() {
        subscription.request(requestSize)
    }

    fun cancel() {
        subscription.cancel()
    }
}
