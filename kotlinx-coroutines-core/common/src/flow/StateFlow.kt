/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
 * A [Flow] that represents a read-only state with a single updatable data [value] that emits updates
 * to the value to its collectors. The current value can be retrieved via [value] property.
 * The flow of future updates to the value can be observed by collecting values from this flow.
 *
 * A [mutable state flow][MutableStateFlow] is created using `MutableStateFlow(value)` constructor function with
 * the initial value. The value of mutable state flow can be  updated by setting its [value] property.
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
 *     val counter: StateFlow<Int> get() = _counter // publicly exposed as read-only state flow
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
 * ### Strong equality-based conflation
 *
 * Values in state flow are conflated using [Any.equals] comparison in a similar way to
 * [distinctUntilChanged] operator. It is used to conflate incoming updates
 * to [value][MutableStateFlow.value] in [MutableStateFlow] and to suppress emission of the values to collectors
 * when new value is equal to the previously emitted one. State flow behavior with classes that violate
 * the contract for [Any.equals] is unspecified.
 *
 * ### StateFlow vs ConflatedBroadcastChannel
 *
 * Conceptually state flow is similar to
 * [ConflatedBroadcastChannel][kotlinx.coroutines.channels.ConflatedBroadcastChannel]
 * and is designed to completely replace `ConflatedBroadcastChannel` in the future.
 * It has the following important difference:
 *
 * * `StateFlow` is simpler, because it does not have to implement all the [Channel] APIs, which allows
 *   for faster, garbage-free implementation, unlike `ConflatedBroadcastChannel` implementation that
 *   allocates objects on each emitted value.
 * * `StateFlow` always has a value which can be safely read at any time via [value] property.
 *    Unlike `ConflatedBroadcastChannel`, there is no way to create a state flow without a value.
 * * `StateFlow` has a clear separation into a read-only `StateFlow` interface and a [MutableStateFlow].
 * * `StateFlow` conflation is based on equality like [distinctUntilChanged] operator,
 *    unlike conflation in `ConflatedBroadcastChannel` that is based on reference identity.
 * * `StateFlow` cannot be currently closed like `ConflatedBroadcastChannel` and can never represent a failure.
 *    This feature might be added in the future if enough compelling use-cases are found.
 *
 * `StateFlow` is designed to better cover typical use-cases of keeping track of state changes in time, taking
 * more pragmatic design choices for the sake of convenience.
 *
 * ### Concurrency
 *
 * All methods of data flow are **thread-safe** and can be safely invoked from concurrent coroutines without
 * external synchronization.
 *
 * ### Operator fusion
 *
 * Application of [flowOn][Flow.flowOn], [conflate][Flow.conflate],
 * [buffer] with [CONFLATED][Channel.CONFLATED] or [RENDEZVOUS][Channel.RENDEZVOUS] capacity,
 * or a [distinctUntilChanged][Flow.distinctUntilChanged] operator has no effect on the state flow.
 * 
 * ### Implementation notes
 *
 * State flow implementation is optimized for memory consumption and allocation-freedom. It uses a lock to ensure
 * thread-safety, but suspending collector coroutines are resumed outside of this lock to avoid dead-locks when
 * using unconfined coroutines. Adding new collectors has `O(1)` amortized cost, but updating a [value] has `O(N)`
 * cost, where `N` is the number of active collectors.
 *
 * ### Not stable for inheritance
 *
 * **`StateFlow` interface is not stable for inheritance in 3rd party libraries**, as new methods
 * might be added to this interface in the future, but is stable for use.
 * Use `MutableStateFlow()` constructor function to create an implementation.
 */
@ExperimentalCoroutinesApi
public interface StateFlow<out T> : Flow<T> {
    /**
     * The current value of this state flow.
     */
    public val value: T
}

/**
 * A mutable [StateFlow] that provides a setter for [value].
 *
 * See [StateFlow] documentation for details.
 *
 * ### Not stable for inheritance
 *
 * **`MutableStateFlow` interface is not stable for inheritance in 3rd party libraries**, as new methods
 * might be added to this interface in the future, but is stable for use.
 * Use `MutableStateFlow()` constructor function to create an implementation.
 */
@ExperimentalCoroutinesApi
public interface MutableStateFlow<T> : StateFlow<T> {
    /**
     * The current value of this state flow.
     *
     * Setting a value that is [equal][Any.equals] to the previous one does nothing.
     */
    public override var value: T
}

/**
 * Creates a [MutableStateFlow] with the given initial [value].
 */
@Suppress("FunctionName")
@ExperimentalCoroutinesApi
public fun <T> MutableStateFlow(value: T): MutableStateFlow<T> = StateFlowImpl(value ?: NULL)

// ------------------------------------ Implementation ------------------------------------

@SharedImmutable
private val NONE = Symbol("NONE")

@SharedImmutable
private val PENDING = Symbol("PENDING")

private const val INITIAL_SIZE = 2 // optimized for just a few collectors

// StateFlow slots are allocated for its collectors
private class StateFlowSlot {
    /**
     * Each slot can have one of the following states:
     *
     * * `null` -- it is not used right now. Can [allocate] to new collector.
     * * `NONE` -- used by a collector, but neither suspended nor has pending value.
     * * `PENDING` -- pending to process new value.
     * * `CancellableContinuationImpl<Unit>` -- suspended waiting for new value.
     *
     * It is important that default `null` value is used, because there can be a race between allocation
     * of a new slot and trying to do [makePending] on this slot.
     */
    private val _state = atomic<Any?>(null)

    fun allocate(): Boolean {
        // No need for atomic check & update here, since allocated happens under StateFlow lock
        if (_state.value != null) return false // not free
        _state.value = NONE // allocated
        return true
    }

    fun free() {
        _state.value = null // free now
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

private class StateFlowImpl<T>(initialValue: Any) : SynchronizedObject(), MutableStateFlow<T>, FusibleFlow<T> {
    private val _state = atomic(initialValue) // T | NULL
    private var sequence = 0 // serializes updates, value update is in process when sequence is odd
    private var slots = arrayOfNulls<StateFlowSlot?>(INITIAL_SIZE)
    private var nSlots = 0 // number of allocated (!free) slots
    private var nextIndex = 0 // oracle for the next free slot index

    @Suppress("UNCHECKED_CAST")
    public override var value: T
        get() = NULL.unbox(_state.value)
        set(value) {
            var curSequence = 0
            var curSlots: Array<StateFlowSlot?> = this.slots // benign race, we will not use it
            val newState = value ?: NULL
            synchronized(this) {
                val oldState = _state.value
                if (oldState == newState) return // Don't do anything if value is not changing
                _state.value = newState
                curSequence = sequence
                if (curSequence and 1 == 0) { // even sequence means quiescent state flow (no ongoing update)
                    curSequence++ // make it odd
                    sequence = curSequence
                } else {
                    // update is already in process, notify it, and return
                    sequence = curSequence + 2 // change sequence to notify, keep it odd
                    return
                }
                curSlots = slots // read current reference to collectors under lock
            }
            /*
               Fire value updates outside of the lock to avoid deadlocks with unconfined coroutines
               Loop until we're done firing all the changes. This is sort of simple flat combining that
               ensures sequential firing of concurrent updates and avoids the storm of collector resumes
               when updates happen concurrently from many threads.
             */
            while (true) {
                // Benign race on element read from array
                for (col in curSlots) {
                    col?.makePending()
                }
                // check if the value was updated again while we were updating the old one
                synchronized(this) {
                    if (sequence == curSequence) { // nothing changed, we are done
                        sequence = curSequence + 1 // make sequence even again
                        return // done
                    }
                    // reread everything for the next loop under the lock
                    curSequence = sequence
                    curSlots = slots
                }
            }
        }

    override suspend fun collect(collector: FlowCollector<T>) {
        val slot = allocateSlot()
        var prevState: Any? = null // previously emitted T!! | NULL (null -- nothing emitted yet)
        try {
            // The loop is arranged so that it starts delivering current value without waiting first
            while (true) {
                // Here the coroutine could have waited for a while to be dispatched,
                // so we use the most recent state here to ensure the best possible conflation of stale values
                val newState = _state.value
                // Conflate value emissions using equality
                if (prevState == null || newState != prevState) {
                    collector.emit(NULL.unbox(newState))
                    prevState = newState
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

    private fun allocateSlot(): StateFlowSlot = synchronized(this) {
        val size = slots.size
        if (nSlots >= size) slots = slots.copyOf(2 * size)
        var index = nextIndex
        var slot: StateFlowSlot
        while (true) {
            slot = slots[index] ?: StateFlowSlot().also { slots[index] = it }
            index++
            if (index >= slots.size) index = 0
            if (slot.allocate()) break // break when found and allocated free slot
        }
        nextIndex = index
        nSlots++
        slot
    }

    private fun freeSlot(slot: StateFlowSlot): Unit = synchronized(this) {
        slot.free()
        nSlots--
    }

    override fun fuse(context: CoroutineContext, capacity: Int): FusibleFlow<T> {
        // context is irrelevant for state flow and it is always conflated
        // so it should not do anything unless buffering is requested
        return when (capacity) {
            Channel.CONFLATED, Channel.RENDEZVOUS -> this
            else -> ChannelFlowOperatorImpl(this, context, capacity)
        }
    }
}
