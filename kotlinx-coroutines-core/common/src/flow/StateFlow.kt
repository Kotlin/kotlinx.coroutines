/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.native.concurrent.*

/**
 * A [SharedFlow] that represents a read-only state with a single updatable data [value] that emits updates
 * to the value to its collectors. A state flow is a _hot_ flow because its active instance exists independently
 * of the presence of collectors. Its current value can be retrieved via the [value] property.
 *
 * **State flow never completes**. A call to [Flow.collect] on a state flow never completes normally, and
 * neither does a coroutine started by the [Flow.launchIn] function. An active collector of a state flow is called a _subscriber_.
 *
 * A [mutable state flow][MutableStateFlow] is created using `MutableStateFlow(value)` constructor function with
 * the initial value. The value of mutable state flow can be updated by setting its [value] property.
 * Updates to the [value] are always [conflated][Flow.conflate]. So a slow collector skips fast updates,
 * but always collects the most recently emitted value.
 *
 * [StateFlow] is useful as a data-model class to represent any kind of state.
 * Derived values can be defined using various operators on the flows, with [combine] operator being especially
 * useful to combine values from multiple state flows using arbitrary functions.
 *
 * For example, the following class encapsulates an integer state and increments its value on each call to `inc`:
 *
 * ```
 * class CounterModel {
 *     private val _counter = MutableStateFlow(0) // private mutable state flow
 *     val counter = _counter.asStateFlow() // publicly exposed as read-only state flow
 *
 *     fun inc() {
 *         _counter.value++
 *     }
 * }
 * ```
 *
 * Having two instances of the above `CounterModel` class one can define the sum of their counters like this:
 *
 * ```
 * val aModel = CounterModel()
 * val bModel = CounterModel()
 * val sumFlow: Flow<Int> = aModel.counter.combine(bModel.counter) { a, b -> a + b }
 * ```
 *
 * As an alternative to the above usage with the `MutableStateFlow(...)` constructor function,
 * any _cold_ [Flow] can be converted to a state flow using the [stateIn] operator.
 *
 * ### Strong equality-based conflation
 *
 * Values in state flow are conflated using [Any.equals] comparison in a similar way to
 * [distinctUntilChanged] operator. It is used to conflate incoming updates
 * to [value][MutableStateFlow.value] in [MutableStateFlow] and to suppress emission of the values to collectors
 * when new value is equal to the previously emitted one. State flow behavior with classes that violate
 * the contract for [Any.equals] is unspecified.
 *
 * ### State flow is a shared flow
 *
 * State flow is a special-purpose, high-performance, and efficient implementation of [SharedFlow] for the narrow,
 * but widely used case of sharing a state. See the [SharedFlow] documentation for the basic rules,
 * constraints, and operators that are applicable to all shared flows.
 *
 * State flow always has an initial value, replays one most recent value to new subscribers, does not buffer any
 * more values, but keeps the last emitted one, and does not support [resetReplayCache][MutableSharedFlow.resetReplayCache].
 * A state flow behaves identically to a shared flow when it is created
 * with the following parameters and the [distinctUntilChanged] operator is applied to it:
 *
 * ```
 * // MutableStateFlow(initialValue) is a shared flow with the following parameters:
 * val shared = MutableSharedFlow(
 *     replay = 1,
 *     onBufferOverflow = BufferOverflow.DROP_OLDEST
 * )
 * shared.tryEmit(initialValue) // emit the initial value
 * val state = shared.distinctUntilChanged() // get StateFlow-like behavior
 * ```
 *
 * Use [SharedFlow] when you need a [StateFlow] with tweaks in its behavior such as extra buffering, replaying more
 * values, or omitting the initial value.
 * 
 * ### StateFlow vs ConflatedBroadcastChannel
 *
 * Conceptually, state flow is similar to [ConflatedBroadcastChannel]
 * and is designed to completely replace it.
 * It has the following important differences:
 *
 * * `StateFlow` is simpler, because it does not have to implement all the [Channel] APIs, which allows
 *   for faster, garbage-free implementation, unlike `ConflatedBroadcastChannel` implementation that
 *   allocates objects on each emitted value.
 * * `StateFlow` always has a value which can be safely read at any time via [value] property.
 *    Unlike `ConflatedBroadcastChannel`, there is no way to create a state flow without a value.
 * * `StateFlow` has a clear separation into a read-only `StateFlow` interface and a [MutableStateFlow].
 * * `StateFlow` conflation is based on equality like [distinctUntilChanged] operator,
 *    unlike conflation in `ConflatedBroadcastChannel` that is based on reference identity.
 * * `StateFlow` cannot be closed like `ConflatedBroadcastChannel` and can never represent a failure.
 *    All errors and completion signals should be explicitly _materialized_ if needed.
 *
 * `StateFlow` is designed to better cover typical use-cases of keeping track of state changes in time, taking
 * more pragmatic design choices for the sake of convenience.
 *
 * To migrate [ConflatedBroadcastChannel] usage to [StateFlow], start by replacing usages of the `ConflatedBroadcastChannel()`
 * constructor with `MutableStateFlow(initialValue)`, using `null` as an initial value if you don't have one.
 * Replace [send][ConflatedBroadcastChannel.send] and [trySend][ConflatedBroadcastChannel.trySend] calls
 * with updates to the state flow's [MutableStateFlow.value], and convert subscribers' code to flow operators.
 * You can use the [filterNotNull] operator to mimic behavior of a `ConflatedBroadcastChannel` without initial value.
 *
 * ### Concurrency
 *
 * All methods of state flow are **thread-safe** and can be safely invoked from concurrent coroutines without
 * external synchronization.
 *
 * ### Operator fusion
 *
 * Application of [flowOn][Flow.flowOn], [conflate][Flow.conflate],
 * [buffer] with [CONFLATED][Channel.CONFLATED] or [RENDEZVOUS][Channel.RENDEZVOUS] capacity,
 * [distinctUntilChanged][Flow.distinctUntilChanged], or [cancellable] operators to a state flow has no effect.
 * 
 * ### Implementation notes
 *
 * State flow implementation is optimized for memory consumption and allocation-freedom. It uses a lock to ensure
 * thread-safety, but suspending collector coroutines are resumed outside of this lock to avoid dead-locks when
 * using unconfined coroutines. Adding new subscribers has `O(1)` amortized cost, but updating a [value] has `O(N)`
 * cost, where `N` is the number of active subscribers.
 *
 * ### Not stable for inheritance
 *
 * **`The StateFlow` interface is not stable for inheritance in 3rd party libraries**, as new methods
 * might be added to this interface in the future, but is stable for use.
 * Use the `MutableStateFlow(value)` constructor function to create an implementation.
 */
public interface StateFlow<out T> : SharedFlow<T> {
    /**
     * The current value of this state flow.
     */
    public val value: T
}

/**
 * A mutable [StateFlow] that provides a setter for [value].
 * An instance of `MutableStateFlow` with the given initial `value` can be created using
 * `MutableStateFlow(value)` constructor function.
 *
 * See the [StateFlow] documentation for details on state flows.
 *
 * ### Not stable for inheritance
 *
 * **The `MutableStateFlow` interface is not stable for inheritance in 3rd party libraries**, as new methods
 * might be added to this interface in the future, but is stable for use.
 * Use the `MutableStateFlow()` constructor function to create an implementation.
 */
public interface MutableStateFlow<T> : StateFlow<T>, MutableSharedFlow<T> {
    /**
     * The current value of this state flow.
     *
     * Setting a value that is [equal][Any.equals] to the previous one does nothing.
     *
     * This property is **thread-safe** and can be safely updated from concurrent coroutines without
     * external synchronization.
     */
    public override var value: T

    /**
     * Atomically compares the current [value] with [expect] and sets it to [update] if it is equal to [expect].
     * The result is `true` if the [value] was set to [update] and `false` otherwise.
     *
     * This function use a regular comparison using [Any.equals]. If both [expect] and [update] are equal to the
     * current [value], this function returns `true`, but it does not actually change the reference that is
     * stored in the [value].
     *
     * This method is **thread-safe** and can be safely invoked from concurrent coroutines without
     * external synchronization.
     */
    public fun compareAndSet(expect: T, update: T): Boolean
}

/**
 * Creates a [MutableStateFlow] with the given initial [value].
 */
@Suppress("FunctionName")
public fun <T> MutableStateFlow(value: T): MutableStateFlow<T> = StateFlowImpl(value ?: NULL)

// ------------------------------------ Implementation ------------------------------------

@SharedImmutable
private val NONE = Symbol("NONE")

@SharedImmutable
private val PENDING = Symbol("PENDING")

// StateFlow slots are allocated for its collectors
private class StateFlowSlot : AbstractSharedFlowSlot<StateFlowImpl<*>>() {
    /**
     * Each slot can have one of the following states:
     *
     * * `null` -- it is not used right now. Can [allocateLocked] to new collector.
     * * `NONE` -- used by a collector, but neither suspended nor has pending value.
     * * `PENDING` -- pending to process new value.
     * * `CancellableContinuationImpl<Unit>` -- suspended waiting for new value.
     *
     * It is important that default `null` value is used, because there can be a race between allocation
     * of a new slot and trying to do [makePending] on this slot.
     */
    private val _state = atomic<Any?>(null)

    override fun allocateLocked(flow: StateFlowImpl<*>): Boolean {
        // No need for atomic check & update here, since allocated happens under StateFlow lock
        if (_state.value != null) return false // not free
        _state.value = NONE // allocated
        return true
    }

    override fun freeLocked(flow: StateFlowImpl<*>): Array<Continuation<Unit>?> {
        _state.value = null // free now
        return EMPTY_RESUMES // nothing more to do
    }

    @Suppress("UNCHECKED_CAST")
    fun makePending() {
        _state.loop { state ->
            when {
                state == null -> return // this slot is free - skip it
                state === PENDING -> return // already pending, nothing to do
                state === NONE -> { // mark as pending
                    if (_state.compareAndSet(state, PENDING)) return
                }
                else -> { // must be a suspend continuation state
                    // we must still use CAS here since continuation may get cancelled and free the slot at any time
                    if (_state.compareAndSet(state, NONE)) {
                        (state as CancellableContinuationImpl<Unit>).resume(Unit)
                        return
                    }
                }
            }
        }
    }

    fun takePending(): Boolean = _state.getAndSet(NONE)!!.let { state ->
        assert { state !is CancellableContinuationImpl<*> }
        return state === PENDING
    }

    @Suppress("UNCHECKED_CAST")
    suspend fun awaitPending(): Unit = suspendCancellableCoroutine sc@ { cont ->
        assert { _state.value !is CancellableContinuationImpl<*> } // can be NONE or PENDING
        if (_state.compareAndSet(NONE, cont)) return@sc // installed continuation, waiting for pending
        // CAS failed -- the only possible reason is that it is already in pending state now
        assert { _state.value === PENDING }
        cont.resume(Unit)
    }
}

private class StateFlowImpl<T>(
    initialState: Any // T | NULL
) : AbstractSharedFlow<StateFlowSlot>(), MutableStateFlow<T>, CancellableFlow<T>, FusibleFlow<T> {
    private val _state = atomic(initialState) // T | NULL
    private var sequence = 0 // serializes updates, value update is in process when sequence is odd

    @Suppress("UNCHECKED_CAST")
    public override var value: T
        get() = NULL.unbox(_state.value)
        set(value) { updateState(null, value ?: NULL) }

    override fun compareAndSet(expect: T, update: T): Boolean =
        updateState(expect ?: NULL, update ?: NULL)

    private fun updateState(expectedState: Any?, newState: Any): Boolean {
        var curSequence = 0
        var curSlots: Array<StateFlowSlot?>? = this.slots // benign race, we will not use it
        synchronized(this) {
            val oldState = _state.value
            if (expectedState != null && oldState != expectedState) return false // CAS support
            if (oldState == newState) return true // Don't do anything if value is not changing, but CAS -> true
            _state.value = newState
            curSequence = sequence
            if (curSequence and 1 == 0) { // even sequence means quiescent state flow (no ongoing update)
                curSequence++ // make it odd
                sequence = curSequence
            } else {
                // update is already in process, notify it, and return
                sequence = curSequence + 2 // change sequence to notify, keep it odd
                return true // updated
            }
            curSlots = slots // read current reference to collectors under lock
        }
        /*
           Fire value updates outside of the lock to avoid deadlocks with unconfined coroutines.
           Loop until we're done firing all the changes. This is a sort of simple flat combining that
           ensures sequential firing of concurrent updates and avoids the storm of collector resumes
           when updates happen concurrently from many threads.
         */
        while (true) {
            // Benign race on element read from array
            curSlots?.forEach {
                it?.makePending()
            }
            // check if the value was updated again while we were updating the old one
            synchronized(this) {
                if (sequence == curSequence) { // nothing changed, we are done
                    sequence = curSequence + 1 // make sequence even again
                    return true // done, updated
                }
                // reread everything for the next loop under the lock
                curSequence = sequence
                curSlots = slots
            }
        }
    }

    override val replayCache: List<T>
        get() = listOf(value)

    override fun tryEmit(value: T): Boolean {
        this.value = value
        return true
    }

    override suspend fun emit(value: T) {
        this.value = value
    }

    @Suppress("UNCHECKED_CAST")
    override fun resetReplayCache() {
        throw UnsupportedOperationException("MutableStateFlow.resetReplayCache is not supported")
    }

    override suspend fun collect(collector: FlowCollector<T>) {
        val slot = allocateSlot()
        try {
            if (collector is SubscribedFlowCollector) collector.onSubscription()
            val collectorJob = currentCoroutineContext()[Job]
            var oldState: Any? = null // previously emitted T!! | NULL (null -- nothing emitted yet)
            // The loop is arranged so that it starts delivering current value without waiting first
            while (true) {
                // Here the coroutine could have waited for a while to be dispatched,
                // so we use the most recent state here to ensure the best possible conflation of stale values
                val newState = _state.value
                // always check for cancellation
                collectorJob?.ensureActive()
                // Conflate value emissions using equality
                if (oldState == null || oldState != newState) {
                    collector.emit(NULL.unbox(newState))
                    oldState = newState
                }
                // Note: if awaitPending is cancelled, then it bails out of this loop and calls freeSlot
                if (!slot.takePending()) { // try fast-path without suspending first
                    slot.awaitPending() // only suspend for new values when needed
                }
            }
        } finally {
            freeSlot(slot)
        }
    }

    override fun createSlot() = StateFlowSlot()
    override fun createSlotArray(size: Int): Array<StateFlowSlot?> = arrayOfNulls(size)

    override fun fuse(context: CoroutineContext, capacity: Int, onBufferOverflow: BufferOverflow) =
        fuseStateFlow(context, capacity, onBufferOverflow)
}

internal fun MutableStateFlow<Int>.increment(delta: Int) {
    while (true) { // CAS loop
        val current = value
        if (compareAndSet(current, current + delta)) return
    }
}

internal fun <T> StateFlow<T>.fuseStateFlow(
    context: CoroutineContext,
    capacity: Int,
    onBufferOverflow: BufferOverflow
): Flow<T> {
    // state flow is always conflated so additional conflation does not have any effect
    assert { capacity != Channel.CONFLATED } // should be desugared by callers
    if ((capacity in 0..1 || capacity == Channel.BUFFERED) && onBufferOverflow == BufferOverflow.DROP_OLDEST) {
        return this
    }
    return fuseSharedFlow(context, capacity, onBufferOverflow)
}
