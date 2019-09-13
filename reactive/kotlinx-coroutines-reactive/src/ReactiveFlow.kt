/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.intrinsics.*
import org.reactivestreams.*
import java.util.*
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
public fun <T : Any> Publisher<T>.asFlow(): Flow<T> =
    PublisherAsFlow(this, 1)

/**
 * Transforms the given flow to a spec-compliant [Publisher].
 */
public fun <T : Any> Flow<T>.asPublisher(): Publisher<T> = FlowAsPublisher(this)

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
        val channel = publisher
            .injectCoroutineContext(scope.coroutineContext)
            .openSubscription(capacity)
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
        publisher.injectCoroutineContext(coroutineContext).subscribe(subscriber)
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

// ContextInjector service is implemented in `kotlinx-coroutines-reactor` module only.
// If `kotlinx-coroutines-reactor` module is not included, the list is empty.
private val contextInjectors: List<ContextInjector> =
    ServiceLoader.load(ContextInjector::class.java, ContextInjector::class.java.classLoader).toList()

private fun <T> Publisher<T>.injectCoroutineContext(coroutineContext: CoroutineContext) =
    contextInjectors.fold(this) { pub, contextInjector -> contextInjector.injectCoroutineContext(pub, coroutineContext) }


/**
 * Adapter that transforms [Flow] into TCK-complaint [Publisher].
 * [cancel] invocation cancels the original flow.
 */
@Suppress("PublisherImplementation")
private class FlowAsPublisher<T : Any>(private val flow: Flow<T>) : Publisher<T> {
    override fun subscribe(subscriber: Subscriber<in T>?) {
        if (subscriber == null) throw NullPointerException()
        subscriber.onSubscribe(FlowSubscription(flow, subscriber))
    }
}

/** @suppress */
@InternalCoroutinesApi
public class FlowSubscription<T>(
    @JvmField val flow: Flow<T>,
    @JvmField val subscriber: Subscriber<in T>
) : Subscription, AbstractCoroutine<Unit>(Dispatchers.Unconfined, false) {
    private val requested = atomic(0L)
    private val producer = atomic<CancellableContinuation<Unit>?>(null)

    override fun onStart() {
        ::flowProcessing.startCoroutineCancellable(this)
    }

    private suspend fun flowProcessing() {
        try {
            consumeFlow()
            subscriber.onComplete()
        } catch (e: Throwable) {
            try {
                if (e is CancellationException) {
                    subscriber.onComplete()
                } else {
                    subscriber.onError(e)
                }
            } catch (e: Throwable) {
                // Last ditch report
                handleCoroutineException(coroutineContext, e)
            }
        }
    }

    /*
     * This method has at most one caller at any time (triggered from the `request` method)
     */
    private suspend fun consumeFlow() {
        flow.collect { value ->
            /*
             * Flow is scopeless, thus if it's not active, its subscription was cancelled.
             * No intermediate "child failed, but flow coroutine is not" states are allowed.
             */
            coroutineContext.ensureActive()
            if (requested.value <= 0L) {
                suspendCancellableCoroutine<Unit> {
                    producer.value = it
                    if (requested.value != 0L) it.resumeSafely()
                }
            }
            requested.decrementAndGet()
            subscriber.onNext(value)
        }
    }

    override fun cancel() {
        cancel(null)
    }

    override fun request(n: Long) {
        if (n <= 0) {
            return
        }
        start()
        requested.update { value ->
            val newValue = value + n
            if (newValue <= 0L) Long.MAX_VALUE else newValue
        }
        val producer = producer.getAndSet(null) ?: return
        producer.resumeSafely()
    }

    private fun CancellableContinuation<Unit>.resumeSafely() {
        val token = tryResume(Unit)
        if (token != null) {
            completeResume(token)
        }
    }
}
