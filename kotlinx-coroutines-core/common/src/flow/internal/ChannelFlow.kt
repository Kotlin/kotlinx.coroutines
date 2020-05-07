/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.jvm.*

internal fun <T> Flow<T>.asChannelFlow(): ChannelFlow<T> =
    this as? ChannelFlow ?: ChannelFlowOperatorImpl(this)

/**
 * Operators that can fuse with [buffer] and [flowOn] operators implement this interface.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public interface FusibleFlow<T> : Flow<T> {
    /**
     * This function is called by [flowOn] (with context) and [buffer] (with capacity) operators
     * that are applied to this flow.
     */
    public fun fuse(
        context: CoroutineContext = EmptyCoroutineContext,
        capacity: Int = Channel.OPTIONAL_CHANNEL
    ): FusibleFlow<T>
}

/**
 * Operators that use channels extend this `ChannelFlow` and are always fused with each other.
 * This class servers as a skeleton implementation of [FusibleFlow] and provides other cross-cutting
 * methods like ability to [produceIn] and [broadcastIn] the corresponding flow, thus making it
 * possible to directly use the backing channel if it exists (hence the `ChannelFlow` name).
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public abstract class ChannelFlow<T>(
    // upstream context
    @JvmField public val context: CoroutineContext,
    // buffer capacity between upstream and downstream context
    @JvmField public val capacity: Int
) : FusibleFlow<T> {

    // shared code to create a suspend lambda from collectTo function in one place
    internal val collectToFun: suspend (ProducerScope<T>) -> Unit
        get() = { collectTo(it) }

    private val produceCapacity: Int
        get() = if (capacity == Channel.OPTIONAL_CHANNEL) Channel.BUFFERED else capacity

    public override fun fuse(context: CoroutineContext, capacity: Int): FusibleFlow<T> {
        // note: previous upstream context (specified before) takes precedence
        val newContext = context + this.context
        val newCapacity = when {
            this.capacity == Channel.OPTIONAL_CHANNEL -> capacity
            capacity == Channel.OPTIONAL_CHANNEL -> this.capacity
            this.capacity == Channel.BUFFERED -> capacity
            capacity == Channel.BUFFERED -> this.capacity
            this.capacity == Channel.CONFLATED -> Channel.CONFLATED
            capacity == Channel.CONFLATED -> Channel.CONFLATED
            else -> {
                // sanity checks
                assert { this.capacity >= 0 }
                assert { capacity >= 0 }
                // combine capacities clamping to UNLIMITED on overflow
                val sum = this.capacity + capacity
                if (sum >= 0) sum else Channel.UNLIMITED // unlimited on int overflow
            }
        }
        if (newContext == this.context && newCapacity == this.capacity) return this
        return create(newContext, newCapacity)
    }

    protected abstract fun create(context: CoroutineContext, capacity: Int): ChannelFlow<T>

    protected abstract suspend fun collectTo(scope: ProducerScope<T>)

    public open fun broadcastImpl(scope: CoroutineScope, start: CoroutineStart): BroadcastChannel<T> =
        scope.broadcast(context, produceCapacity, start, block = collectToFun)

    /**
     * Here we use ATOMIC start for a reason (#1825).
     * NB: [produceImpl] is used for [flowOn].
     * For non-atomic start it is possible to observe the situation,
     * where the pipeline after the [flowOn] call successfully executes (mostly, its `onCompletion`)
     * handlers, while the pipeline before does not, because it was cancelled during its dispatch.
     * Thus `onCompletion` and `finally` blocks won't be executed and it may lead to a different kinds of memory leaks.
     */
    public open fun produceImpl(scope: CoroutineScope): ReceiveChannel<T> =
        scope.produce(context, produceCapacity, start = CoroutineStart.ATOMIC, block = collectToFun)

    override suspend fun collect(collector: FlowCollector<T>): Unit =
        coroutineScope {
            collector.emitAll(produceImpl(this))
        }

    public open fun additionalToStringProps(): String = ""

    // debug toString
    override fun toString(): String =
        "$classSimpleName[${additionalToStringProps()}context=$context, capacity=$capacity]"
}

// ChannelFlow implementation that operates on another flow before it
internal abstract class ChannelFlowOperator<S, T>(
    @JvmField val flow: Flow<S>,
    context: CoroutineContext,
    capacity: Int
) : ChannelFlow<T>(context, capacity) {
    protected abstract suspend fun flowCollect(collector: FlowCollector<T>)

    // Changes collecting context upstream to the specified newContext, while collecting in the original context
    private suspend fun collectWithContextUndispatched(collector: FlowCollector<T>, newContext: CoroutineContext) {
        val originalContextCollector = collector.withUndispatchedContextCollector(coroutineContext)
        // invoke flowCollect(originalContextCollector) in the newContext
        return withContextUndispatched(newContext, block = { flowCollect(it) }, value = originalContextCollector)
    }

    // Slow path when output channel is required
    protected override suspend fun collectTo(scope: ProducerScope<T>) =
        flowCollect(SendingCollector(scope))

    // Optimizations for fast-path when channel creation is optional
    override suspend fun collect(collector: FlowCollector<T>) {
        // Fast-path: When channel creation is optional (flowOn/flowWith operators without buffer)
        if (capacity == Channel.OPTIONAL_CHANNEL) {
            val collectContext = coroutineContext
            val newContext = collectContext + context // compute resulting collect context
            // #1: If the resulting context happens to be the same as it was -- fallback to plain collect
            if (newContext == collectContext)
                return flowCollect(collector)
            // #2: If we don't need to change the dispatcher we can go without channels
            if (newContext[ContinuationInterceptor] == collectContext[ContinuationInterceptor])
                return collectWithContextUndispatched(collector, newContext)
        }
        // Slow-path: create the actual channel
        super.collect(collector)
    }

    // debug toString
    override fun toString(): String = "$flow -> ${super.toString()}"
}

// Simple channel flow operator: flowOn, buffer, or their fused combination
internal class ChannelFlowOperatorImpl<T>(
    flow: Flow<T>,
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = Channel.OPTIONAL_CHANNEL
) : ChannelFlowOperator<T, T>(flow, context, capacity) {
    override fun create(context: CoroutineContext, capacity: Int): ChannelFlow<T> =
        ChannelFlowOperatorImpl(flow, context, capacity)

    override suspend fun flowCollect(collector: FlowCollector<T>) =
        flow.collect(collector)
}

// Now if the underlying collector was accepting concurrent emits, then this one is too
// todo: we might need to generalize this pattern for "thread-safe" operators that can fuse with channels
private fun <T> FlowCollector<T>.withUndispatchedContextCollector(emitContext: CoroutineContext): FlowCollector<T> = when (this) {
    // SendingCollector & NopCollector do not care about the context at all and can be used as is
    is SendingCollector, is NopCollector -> this
    // Otherwise just wrap into UndispatchedContextCollector interface implementation
    else -> UndispatchedContextCollector(this, emitContext)
}

private class UndispatchedContextCollector<T>(
    downstream: FlowCollector<T>,
    private val emitContext: CoroutineContext
) : FlowCollector<T> {
    private val countOrElement = threadContextElements(emitContext) // precompute for fast withContextUndispatched
    private val emitRef: suspend (T) -> Unit = { downstream.emit(it) } // allocate suspend function ref once on creation

    override suspend fun emit(value: T): Unit =
        withContextUndispatched(emitContext, countOrElement, emitRef, value)
}

// Efficiently computes block(value) in the newContext
private suspend fun <T, V> withContextUndispatched(
    newContext: CoroutineContext,
    countOrElement: Any = threadContextElements(newContext), // can be precomputed for speed
    block: suspend (V) -> T, value: V
): T =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        withCoroutineContext(newContext, countOrElement) {
            block.startCoroutineUninterceptedOrReturn(value, Continuation(newContext) {
                uCont.resumeWith(it)
            })
        }
    }
