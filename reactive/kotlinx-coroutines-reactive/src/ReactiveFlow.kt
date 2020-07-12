/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
 * More precisely, it specifies the value of the subscription's [request][Subscription.request].
 * [buffer] default capacity is used by default.
 *
 * If any of the resulting flow transformations fails, subscription is immediately cancelled and all in-flight elements
 * are discarded.
 *
 * This function is integrated with `ReactorContext` from `kotlinx-coroutines-reactor` module,
 * see its documentation for additional details.
 */
public fun <T : Any> Publisher<T>.asFlow(): Flow<T> =
    PublisherAsFlow(this)

/**
 * Transforms the given flow to a reactive specification compliant [Publisher].
 *
 * This function is integrated with `ReactorContext` from `kotlinx-coroutines-reactor` module,
 * see its documentation for additional details.
 */
public fun <T : Any> Flow<T>.asPublisher(): Publisher<T> = FlowAsPublisher(this)

private class PublisherAsFlow<T : Any>(
    private val publisher: Publisher<T>,
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = Channel.BUFFERED
) : ChannelFlow<T>(context, capacity) {
    override fun create(context: CoroutineContext, capacity: Int): ChannelFlow<T> =
        PublisherAsFlow(publisher, context, capacity)

    /*
     * Suppress for Channel.CHANNEL_DEFAULT_CAPACITY.
     * It's too counter-intuitive to be public and moving it to Flow companion
     * will also create undesired effect.
     */
    @Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
    private val requestSize: Long
        get() = when (capacity) {
            Channel.CONFLATED -> Long.MAX_VALUE // request all and conflate incoming
            Channel.RENDEZVOUS -> 1L // need to request at least one anyway
            Channel.UNLIMITED -> Long.MAX_VALUE // reactive streams way to say "give all" must be Long.MAX_VALUE
            Channel.BUFFERED -> Channel.CHANNEL_DEFAULT_CAPACITY.toLong()
            else -> capacity.toLong().also { check(it >= 1) }
        }

    override suspend fun collect(collector: FlowCollector<T>) {
        val collectContext = coroutineContext
        val newDispatcher = context[ContinuationInterceptor]
        if (newDispatcher == null || newDispatcher == collectContext[ContinuationInterceptor]) {
            // fast path -- subscribe directly in this dispatcher
            return collectImpl(collectContext + context, collector)
        }
        // slow path -- produce in a separate dispatcher
        collectSlowPath(collector)
    }

    private suspend fun collectSlowPath(collector: FlowCollector<T>) {
        coroutineScope {
            collector.emitAll(produceImpl(this + context))
        }
    }

    private suspend fun collectImpl(injectContext: CoroutineContext, collector: FlowCollector<T>) {
        val subscriber = ReactiveSubscriber<T>(capacity, requestSize)
        // inject subscribe context into publisher
        publisher.injectCoroutineContext(injectContext).subscribe(subscriber)
        try {
            var consumed = 0L
            while (true) {
                val value = subscriber.takeNextOrNull() ?: break
                coroutineContext.ensureActive()
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

    // The second channel here is used for produceIn/broadcastIn and slow-path (dispatcher change)
    override suspend fun collectTo(scope: ProducerScope<T>) =
        collectImpl(scope.coroutineContext, SendingCollector(scope.channel))
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
private val contextInjectors: Array<ContextInjector> =
    ServiceLoader.load(ContextInjector::class.java, ContextInjector::class.java.classLoader)
        .iterator().asSequence()
        .toList().toTypedArray() // R8 opto

internal fun <T> Publisher<T>.injectCoroutineContext(coroutineContext: CoroutineContext) =
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
    @JvmField public val flow: Flow<T>,
    @JvmField public val subscriber: Subscriber<in T>
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
