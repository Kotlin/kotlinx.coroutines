/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.sync.*
import kotlin.coroutines.*

internal class ChannelFlowTransformLatest<T, R>(
    private val transform: suspend FlowCollector<R>.(value: T) -> Unit,
    flow: Flow<T>,
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = Channel.BUFFERED
) : ChannelFlowOperator<T, R>(flow, context, capacity) {
    override fun create(context: CoroutineContext, capacity: Int): ChannelFlow<R> =
        ChannelFlowTransformLatest(transform, flow, context, capacity)

    override suspend fun flowCollect(collector: FlowCollector<R>) {
        flowScope {
            var previousFlow: Job? = null
            flow.collect { value ->
                previousFlow?.apply {
                    cancel(ChildCancelledException())
                    join()
                }
                // Do not pay for dispatch here, it's never necessary
                previousFlow = launch(start = CoroutineStart.UNDISPATCHED) {
                    collector.transform(value)
                }
            }
        }
    }
}

internal class ChannelFlowMerge<T>(
    flow: Flow<Flow<T>>,
    private val concurrency: Int,
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = Channel.OPTIONAL_CHANNEL
) : ChannelFlowOperator<Flow<T>, T>(flow, context, capacity) {
    override fun create(context: CoroutineContext, capacity: Int): ChannelFlow<T> =
        ChannelFlowMerge(flow, concurrency, context, capacity)

    // The actual merge implementation with concurrency limit
    private suspend fun mergeImpl(scope: CoroutineScope, collector: ConcurrentFlowCollector<T>) {
        val semaphore = Semaphore(concurrency)
        val job: Job? = coroutineContext[Job]
        flow.collect { inner ->
            /*
             * We launch a coroutine on each emitted element and the only potential
             * suspension point in this collector is `semaphore.acquire` that rarely suspends,
             * so we manually check for cancellation to propagate it to the upstream in time.
             */
            job?.ensureActive()
            semaphore.acquire()
            scope.launch {
                try {
                    inner.collect(collector)
                } finally {
                    semaphore.release() // Release concurrency permit
                }
            }
        }
    }

    // Fast path in ChannelFlowOperator calls this function (channel was not created yet)
    override suspend fun flowCollect(collector: FlowCollector<T>) {
        // this function should not have been invoked when channel was explicitly requested
        assert { capacity == Channel.OPTIONAL_CHANNEL }
        flowScope {
            mergeImpl(this, collector.asConcurrentFlowCollector())
        }
    }

    // Slow path when output channel is required (and was created)
    override suspend fun collectTo(scope: ProducerScope<T>) =
        mergeImpl(scope, SendingCollector(scope))

    override fun additionalToStringProps(): String =
        "concurrency=$concurrency, "
}
