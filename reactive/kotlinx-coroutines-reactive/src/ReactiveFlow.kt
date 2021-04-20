/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
import kotlinx.coroutines.internal.*

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
 *
 * An optional [context] can be specified to control the execution context of calls to [Subscriber] methods.
 * You can set a [CoroutineDispatcher] to confine them to a specific thread and/or various [ThreadContextElement] to
 * inject additional context into the caller thread. By default, the [Unconfined][Dispatchers.Unconfined] dispatcher
 * is used, so calls are performed from an arbitrary thread.
 */
@JvmOverloads // binary compatibility
public fun <T : Any> Flow<T>.asPublisher(context: CoroutineContext = EmptyCoroutineContext): Publisher<T> =
    FlowAsPublisher(this, Dispatchers.Unconfined + context)

private class PublisherAsFlow<T : Any>(
    private val publisher: Publisher<T>,
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = Channel.BUFFERED,
    onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND
) : ChannelFlow<T>(context, capacity, onBufferOverflow) {
    override fun create(context: CoroutineContext, capacity: Int, onBufferOverflow: BufferOverflow): ChannelFlow<T> =
        PublisherAsFlow(publisher, context, capacity, onBufferOverflow)

    /*
     * Suppress for Channel.CHANNEL_DEFAULT_CAPACITY.
     * It's too counter-intuitive to be public and moving it to Flow companion
     * will also create undesired effect.
     */
    @Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
    private val requestSize: Long
        get() =
            if (onBufferOverflow != BufferOverflow.SUSPEND) {
                Long.MAX_VALUE // request all, since buffering strategy is to never suspend
            } else when (capacity) {
                Channel.RENDEZVOUS -> 1L // need to request at least one anyway
                Channel.UNLIMITED -> Long.MAX_VALUE // reactive streams way to say "give all", must be Long.MAX_VALUE
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
        val subscriber = ReactiveSubscriber<T>(capacity, onBufferOverflow, requestSize)
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

@Suppress("ReactiveStreamsSubscriberImplementation")
private class ReactiveSubscriber<T : Any>(
    capacity: Int,
    onBufferOverflow: BufferOverflow,
    private val requestSize: Long
) : Subscriber<T> {
    private lateinit var subscription: Subscription

    // This implementation of ReactiveSubscriber always uses "offer" in its onNext implementation and it cannot
    // be reliable with rendezvous channel, so a rendezvous channel is replaced with buffer=1 channel
    private val channel = Channel<T>(if (capacity == Channel.RENDEZVOUS) 1 else capacity, onBufferOverflow)

    suspend fun takeNextOrNull(): T? {
        val result = channel.receiveCatching()
        result.exceptionOrNull()?.let { throw it }
        return result.getOrElse { null } // Closed channel
    }

    override fun onNext(value: T) {
        // Controlled by requestSize
        require(channel.trySend(value).isSuccess) { "Element $value was not added to channel because it was full, $channel" }
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
@Suppress("ReactiveStreamsPublisherImplementation")
private class FlowAsPublisher<T : Any>(
    private val flow: Flow<T>,
    private val context: CoroutineContext
) : Publisher<T> {
    override fun subscribe(subscriber: Subscriber<in T>?) {
        if (subscriber == null) throw NullPointerException()
        subscriber.onSubscribe(FlowSubscription(flow, subscriber, context))
    }
}

/** @suppress */
@InternalCoroutinesApi
public class FlowSubscription<T>(
    @JvmField public val flow: Flow<T>,
    @JvmField public val subscriber: Subscriber<in T>,
    context: CoroutineContext
) : Subscription, AbstractCoroutine<Unit>(context, initParentJob = false, true) {
    /*
     * We deliberately set initParentJob to false and do not establish parent-child
     * relationship because FlowSubscription doesn't support it
     */
    private val requested = atomic(0L)
    private val producer = atomic<Continuation<Unit>?>(createInitialContinuation())
    @Volatile
    private var cancellationRequested = false

    // This code wraps startCoroutineCancellable into continuation
    private fun createInitialContinuation(): Continuation<Unit> = Continuation(coroutineContext) {
        ::flowProcessing.startCoroutineCancellable(this)
    }

    private suspend fun flowProcessing() {
        try {
            consumeFlow()
        } catch (cause: Throwable) {
            @Suppress("INVISIBLE_MEMBER")
            val unwrappedCause = unwrap(cause)
            if (!cancellationRequested || isActive || unwrappedCause !== getCancellationException()) {
                try {
                    subscriber.onError(cause)
                } catch (e: Throwable) {
                    // Last ditch report
                    cause.addSuppressed(e)
                    handleCoroutineException(coroutineContext, cause)
                }
            }
            return
        }
        // We only call this if `consumeFlow()` finished successfully
        try {
            subscriber.onComplete()
        } catch (e: Throwable) {
            handleCoroutineException(coroutineContext, e)
        }
    }

    /*
     * This method has at most one caller at any time (triggered from the `request` method)
     */
    private suspend fun consumeFlow() {
        flow.collect { value ->
            // Emit the value
            subscriber.onNext(value)
            // Suspend if needed before requesting the next value
            if (requested.decrementAndGet() <= 0) {
                suspendCancellableCoroutine<Unit> {
                    producer.value = it
                }
            } else {
                // check for cancellation if we don't suspend
                coroutineContext.ensureActive()
            }
        }
    }

    override fun cancel() {
        cancellationRequested = true
        cancel(null)
    }

    override fun request(n: Long) {
        if (n <= 0) return
        val old = requested.getAndUpdate { value ->
            val newValue = value + n
            if (newValue <= 0L) Long.MAX_VALUE else newValue
        }
        if (old <= 0L) {
            assert(old == 0L)
            // Emitter is not started yet or has suspended -- spin on race with suspendCancellableCoroutine
            while (true) {
                val producer = producer.getAndSet(null) ?: continue // spin if not set yet
                producer.resume(Unit)
                break
            }
        }
    }
}
