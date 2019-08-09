/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")

package kotlinx.coroutines.reactive

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.reactivestreams.*
import kotlinx.coroutines.intrinsics.*

/**
 * Transforms the given flow to a spec-compliant [Publisher].
 */
@ExperimentalCoroutinesApi
public fun <T : Any> Flow<T>.asPublisher(): Publisher<T> = FlowAsPublisher(this)

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
