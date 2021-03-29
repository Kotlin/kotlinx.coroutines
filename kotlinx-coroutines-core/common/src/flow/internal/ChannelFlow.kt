/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
 * Operators that can fuse with **downstream** [buffer] and [flowOn] operators implement this interface.
 *
 * @suppress **This an internal API and should not be used from general code.**
 */
@InternalCoroutinesApi
public interface FusibleFlow<T> : Flow<T> {
    /**
     * This function is called by [flowOn] (with context) and [buffer] (with capacity) operators
     * that are applied to this flow. Should not be used with [capacity] of [Channel.CONFLATED]
     * (it shall be desugared to `capacity = 0, onBufferOverflow = DROP_OLDEST`).
     */
    public fun fuse(
        context: CoroutineContext = EmptyCoroutineContext,
        capacity: Int = Channel.OPTIONAL_CHANNEL,
        onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND
    ): Flow<T>
}

/**
 * Operators that use channels as their "output" extend this `ChannelFlow` and are always fused with each other.
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
    @JvmField public val capacity: Int,
    // buffer overflow strategy
    @JvmField public val onBufferOverflow: BufferOverflow
) : FusibleFlow<T> {
    init {
        assert { capacity != Channel.CONFLATED } // CONFLATED must be desugared to 0, DROP_OLDEST by callers
    }

    // shared code to create a suspend lambda from collectTo function in one place
    internal val collectToFun: suspend (ProducerScope<T>) -> Unit
        get() = { collectTo(it) }

    private val produceCapacity: Int
        get() = if (capacity == Channel.OPTIONAL_CHANNEL) Channel.BUFFERED else capacity

    /**
     * When this [ChannelFlow] implementation can work without a channel (supports [Channel.OPTIONAL_CHANNEL]),
     * then it should return a non-null value from this function, so that a caller can use it without the effect of
     * additional [flowOn] and [buffer] operators, by incorporating its
     * [context], [capacity], and [onBufferOverflow] into its own implementation.
     */
    public open fun dropChannelOperators(): Flow<T>? = null

    public override fun fuse(context: CoroutineContext, capacity: Int, onBufferOverflow: BufferOverflow): Flow<T> {
        assert { capacity != Channel.CONFLATED } // CONFLATED must be desugared to (0, DROP_OLDEST) by callers
        // note: previous upstream context (specified before) takes precedence
        val newContext = context + this.context
        val newCapacity: Int
        val newOverflow: BufferOverflow
        if (onBufferOverflow != BufferOverflow.SUSPEND) {
            // this additional buffer never suspends => overwrite preceding buffering configuration
            newCapacity = capacity
            newOverflow = onBufferOverflow
        } else {
            // combine capacities, keep previous overflow strategy
            newCapacity = when {
                this.capacity == Channel.OPTIONAL_CHANNEL -> capacity
                capacity == Channel.OPTIONAL_CHANNEL -> this.capacity
                this.capacity == Channel.BUFFERED -> capacity
                capacity == Channel.BUFFERED -> this.capacity
                else -> {
                    // sanity checks
                    assert { this.capacity >= 0 }
                    assert { capacity >= 0 }
                    // combine capacities clamping to UNLIMITED on overflow
                    val sum = this.capacity + capacity
                    if (sum >= 0) sum else Channel.UNLIMITED // unlimited on int overflow
                }
            }
            newOverflow = this.onBufferOverflow
        }
        if (newContext == this.context && newCapacity == this.capacity && newOverflow == this.onBufferOverflow)
            return this
        return create(newContext, newCapacity, newOverflow)
    }

    protected abstract fun create(context: CoroutineContext, capacity: Int, onBufferOverflow: BufferOverflow): ChannelFlow<T>

    protected abstract suspend fun collectTo(scope: ProducerScope<T>)

    // broadcastImpl is used in broadcastIn operator which is obsolete and replaced by SharedFlow.
    // BroadcastChannel does not support onBufferOverflow beyond simple conflation
    public open fun broadcastImpl(scope: CoroutineScope, start: CoroutineStart): BroadcastChannel<T> {
        val broadcastCapacity = when (onBufferOverflow) {
            BufferOverflow.SUSPEND -> produceCapacity
            BufferOverflow.DROP_OLDEST -> Channel.CONFLATED
            BufferOverflow.DROP_LATEST ->
                throw IllegalArgumentException("Broadcast channel does not support BufferOverflow.DROP_LATEST")
        }
        return scope.broadcast(context, broadcastCapacity, start, block = collectToFun)
    }

    /**
     * Here we use ATOMIC start for a reason (#1825).
     * NB: [produceImpl] is used for [flowOn].
     * For non-atomic start it is possible to observe the situation,
     * where the pipeline after the [flowOn] call successfully executes (mostly, its `onCompletion`)
     * handlers, while the pipeline before does not, because it was cancelled during its dispatch.
     * Thus `onCompletion` and `finally` blocks won't be executed and it may lead to a different kinds of memory leaks.
     */
    public open fun produceImpl(scope: CoroutineScope): ReceiveChannel<T> =
        scope.produce(context, produceCapacity, onBufferOverflow, start = CoroutineStart.ATOMIC, block = collectToFun)

    override suspend fun collect(collector: FlowCollector<T>): Unit =
        coroutineScope {
            collector.emitAll(produceImpl(this))
        }

    protected open fun additionalToStringProps(): String? = null

    // debug toString
    override fun toString(): String {
        val props = ArrayList<String>(4)
        additionalToStringProps()?.let { props.add(it) }
        if (context !== EmptyCoroutineContext) props.add("context=$context")
        if (capacity != Channel.OPTIONAL_CHANNEL) props.add("capacity=$capacity")
        if (onBufferOverflow != BufferOverflow.SUSPEND) props.add("onBufferOverflow=$onBufferOverflow")
        return "$classSimpleName[${props.joinToString(", ")}]"
    }
}

// ChannelFlow implementation that operates on another flow before it
internal abstract class ChannelFlowOperator<S, T>(
    @JvmField protected val flow: Flow<S>,
    context: CoroutineContext,
    capacity: Int,
    onBufferOverflow: BufferOverflow
) : ChannelFlow<T>(context, capacity, onBufferOverflow) {
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

/**
 * Simple channel flow operator: [flowOn], [buffer], or their fused combination.
 */
internal class ChannelFlowOperatorImpl<T>(
    flow: Flow<T>,
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = Channel.OPTIONAL_CHANNEL,
    onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND
) : ChannelFlowOperator<T, T>(flow, context, capacity, onBufferOverflow) {
    override fun create(context: CoroutineContext, capacity: Int, onBufferOverflow: BufferOverflow): ChannelFlow<T> =
        ChannelFlowOperatorImpl(flow, context, capacity, onBufferOverflow)

    override fun dropChannelOperators(): Flow<T>? = flow

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
        withContextUndispatched(emitContext, value, countOrElement, emitRef)
}

// Efficiently computes block(value) in the newContext
internal suspend fun <T, V> withContextUndispatched(
    newContext: CoroutineContext,
    value: V,
    countOrElement: Any = threadContextElements(newContext), // can be precomputed for speed
    block: suspend (V) -> T
): T =
    suspendCoroutineUninterceptedOrReturn { uCont ->
        withCoroutineContext(newContext, countOrElement) {
            block.startCoroutineUninterceptedOrReturn(value, StackFrameContinuation(uCont, newContext))
        }
    }

// Continuation that links the caller with uCont with walkable CoroutineStackFrame
private class StackFrameContinuation<T>(
    private val uCont: Continuation<T>, override val context: CoroutineContext
) : Continuation<T>, CoroutineStackFrame {

    override val callerFrame: CoroutineStackFrame?
        get() = uCont as? CoroutineStackFrame

    override fun resumeWith(result: Result<T>) {
        uCont.resumeWith(result)
    }

    override fun getStackTraceElement(): StackTraceElement? = null
}
