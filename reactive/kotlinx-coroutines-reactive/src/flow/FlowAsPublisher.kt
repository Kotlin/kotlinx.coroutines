/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.reactivestreams.*
import java.util.concurrent.atomic.*

/**
 * Transforms the given flow to a spec-compliant [Publisher]
 */
@JvmName("from")
@FlowPreview
public fun <T : Any> Flow<T>.asPublisher(): Publisher<T> = FlowAsPublisher(this)

/**
 * Adapter that transforms [Flow] into TCK-complaint [Publisher].
 * Any calls to [cancel] cancels the original flow.
 */
@Suppress("PublisherImplementation")
private class FlowAsPublisher<T : Any>(private val flow: Flow<T>) : Publisher<T> {

    override fun subscribe(subscriber: Subscriber<in T>?) {
        if (subscriber == null) throw NullPointerException()
        subscriber.onSubscribe(
            FlowSubscription(
                flow,
                subscriber
            )
        )
    }

    private class FlowSubscription<T>(val flow: Flow<T>, val subscriber: Subscriber<in T>) : Subscription {
        @Volatile
        internal var canceled: Boolean = false
        private val requested = AtomicLong(0L)
        private val producer: AtomicReference<CancellableContinuation<Unit>?> = AtomicReference()

        // This is actually optimizable
        private var job = GlobalScope.launch(Dispatchers.Unconfined, start = CoroutineStart.LAZY) {
            try {
                consumeFlow()
                subscriber.onComplete()
            } catch (e: Throwable) {
                // Failed with real exception
                if (!coroutineContext[Job]!!.isCancelled) {
                    subscriber.onError(e)
                }
            }
        }

        private suspend fun CoroutineScope.consumeFlow() {
            flow.collect { value ->
                if (!isActive) {
                    subscriber.onComplete()
                    yield() // Force cancellation
                }

                if (requested.get() == 0L) {
                    suspendCancellableCoroutine<Unit> {
                        producer.set(it)
                        if (requested.get() != 0L) it.resumeSafely()
                    }
                }

                requested.decrementAndGet()
                val result = kotlin.runCatching {
                    subscriber.onNext(value)
                }

                if (result.isFailure) {
                    subscriber.onError(result.exceptionOrNull())
                }
            }
        }

        override fun cancel() {
            canceled = true
            job.cancel()
        }

        override fun request(n: Long) {
            if (n <= 0) {
                return
            }

            if (canceled) return

            job.start()
            var snapshot: Long
            var newValue: Long
            do {
                snapshot = requested.get()
                newValue = snapshot + n
                if (newValue <= 0L) newValue = Long.MAX_VALUE

            } while (!requested.compareAndSet(snapshot, newValue))

            val prev = producer.get()
            if (prev == null || !producer.compareAndSet(prev, null)) return

            prev.resumeSafely()
        }

        private fun CancellableContinuation<Unit>.resumeSafely() {
            val token = tryResume(Unit)
            if (token != null) {
                completeResume(token)
            }
        }
    }
}
