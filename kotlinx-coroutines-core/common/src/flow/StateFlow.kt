/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*
import kotlin.reflect.*

/**
 * A hot [Flow] that contains and distributes a state of a single [value].
 * It is _hot_, because it exists and maintains its state even without any collectors.
 *
 * A state flow can be created with `StateFlow()` constructor function either without an initial value
 * or with an initial value. In the latter case [isInitialized] returns `true`.
 * The return type of `StateFlow()` function is [MutableStateFlow] that can be updated,
 * while this `StateFlow` interface represent a read-only view.
 *
 * `StateFlow` represents the current state and only the most recent [value] is of interest.
 * Updates to the [value] are always [conflated][Flow.conflate], so a slow collector skips fast updates,
 * but always collects the most recently emitted value.
 *
 * Dependent values can be defined by using various operators on the flows, with [combine] being especially
 * useful to combine multiple state flows using arbitrary functions.
 *
 * A alternative read-only interface to a state flow is a [Flow]. Consider publicly exposing uninitialized state
 * flows as [Flow] to avoid races and the resulting exceptions while attempting to read their [value]. However,
 * publicly exposing an initialized [StateFlow] instance as such is perfectly fine and might be convenient
 * (see below for example).
 * 
 * For example, the following class encapsulates an integer state flow and increments its value on each call to `inc`:
 *
 * ```
 * class CounterModel {
 *     private val _flow = StateFlow(0) // private mutable state flow
 *     val flow: StateFlow<Int> get() = _flow // publicly exposed as a state flow
 *     var value: Int by _flow // publicly exposed value
 *         private set // setting only privately
 *
 *     fun inc() { value++ }
 * }
 * ```
 *
 * Having two instances of the above `CounterModel` class one can define the sum of their counters like this:
 *
 * ```
 * val aModel = CounterModel()
 * val bModel = CounterModel()
 * val sumAAndB = aModel.flow.combine(bModel.flow) { a, b -> a + b }
 * ```
 *
 * Being able to access current state's [value] we can avoid special operations if need to provide a new value of
 * sum only when a's value updated. A simple [map] operation would do in this case:
 *
 * ```
 * val sumAWithB = aModel.flow.map { a -> a + bModel.value }
 * ```
 *
 * Conceptually state flow is similar to
 * [ConflatedBroadcastChannel][kotlinx.coroutines.channels.ConflatedBroadcastChannel]
 * but it is simpler, because it does not have to implement all the channel APIs.
 *
 * All methods of state flow are **thread-safe** and can be safely invoked from concurrent coroutines without
 * external synchronization.
 *
 * ### Operator fusion
 *
 * Application of [flowOn], [conflate], and
 * [buffer] with [CONFLATED][Channel.CONFLATED] or [RENDEZVOUS][Channel.RENDEZVOUS] capacity
 * has no effect on the data flow.
 * 
 * ### Implementation notes
 *
 * State flow implementation is optimized for memory consumption and allocation-freedom. It uses a lock to ensure
 * thread-safety, but suspending collector coroutines are resumed outside of this lock to avoid dead-locks when
 * using unconfined coroutines. Adding new collectors has `O(1)` amortized code, but updating a [value] has `O(N)`
 * cost, where `N` is the number of collectors.
 */
@FlowPreview
public interface StateFlow<T> : Flow<T> {
    /**
     * Value of this flow.
     *
     * Getting a value from an [uninitialized][isInitialized] flow produces [IllegalStateException].
     * Getting a value from a [closed][isClosed] flow produces [IllegalStateException].
     */
    public val value: T

    /**
     * Returns `true` if this flow is initialized.
     *
     * A state flow is initialized when its [value] was set at least once.
     * A [closed][isClosed] state flow is considered to be initialized.
     * See also [MutableStateFlow.value].
     */
    public val isInitialized: Boolean

    /**
     * Returns `true` if this flow is closed.
     *
     * See [MutableStateFlow.close].
     */
    public val isClosed: Boolean
}

/**
 * A mutable hot [Flow] that contains and distributes a state of a single updatable [value].
 *
 * State value can be updated by setting [value] property.
 * Updates to the [value] are always [conflated][Flow.conflate], so a slow collector skips fast updates,
 * but always collects the most recently emitted value.
 *
 * A mutable flow can be [closed][close] and all its collectors will complete.
 *
 * An instance of mutable state flow can be created with `StateFlow()` construction function.
 * See [StateFlow] interface documentation for more details.
 *
 * All methods of state flow are **thread-safe** and can be safely invoked from concurrent coroutines without
 * external synchronization.
 */
public interface MutableStateFlow<T> : StateFlow<T> {
    /**
     * Value of this state flow.
     *
     * Setting a value that is [equal][Any.equals] to the previous one does nothing.
     *
     * Getting a value from an [uninitialized][isInitialized] flow produces [IllegalStateException].
     * Getting a value from or setting a value to a [closed][isClosed] flow produces [IllegalStateException].
     */
    public override var value: T

    /**
     * Closes this state flow.
     * This is an idempotent operation -- subsequent invocations of this function have no effect and return `false`.
     * Conceptually, its sets a value to a special "close token" and all active and future collector from
     * this [Flow] complete either normally (when [cause] is null) or with the corresponding exception that
     * was specified as a [cause].
     */
    public fun close(cause: Throwable? = null): Boolean
}

/**
 * Creates an uninitialized [MutableStateFlow].
 */
@Suppress("FunctionName")
@FlowPreview
public fun <T> StateFlow(): MutableStateFlow<T> = StateFlowImpl(NONE)

/**
 * Creates a [MutableStateFlow] with a given initial [value].
 *
 * This is a shorthand for `StateFlow().apply { this.value = value }`.
 */
@Suppress("FunctionName")
@FlowPreview
public fun <T> StateFlow(value: T): MutableStateFlow<T> = StateFlowImpl(value ?: NULL)

// todo: KDoc
@Suppress("NOTHING_TO_INLINE")
public inline operator fun <T> StateFlow<T>.getValue(thisRef: Any?, prop: KProperty<*>): T = value

// todo: KDoc
@Suppress("NOTHING_TO_INLINE")
public inline operator fun <T> MutableStateFlow<T>.setValue(thisRef: Any?, prop: KProperty<*>, value: T) {
    this.value = value
}

// todo: KDoc
public suspend fun <T> StateFlow<T>.awaitInitialized(): StateFlow<T> {
    if (isInitialized) return this // fast path -- initialized
    // slow path -- suspend
    return awaitInitializedSuspend()
}

private suspend fun <T> StateFlow<T>.awaitInitializedSuspend(): StateFlow<T> {
    first() // just collect the first element
    return this
}

// ============================ private implementation constants and class ============================

@SharedImmutable
private val NONE = Symbol("NONE")

private const val INITIAL_SIZE = 2 // optimized for just a few collectors

// StateFlow slots are allocated for its collectors
private class StateFlowSlot(
    @JvmField val index: Int // its permanent index in StateFlowImpl.slots array
) {
    /**
     * Each slot can have one of the following states:
     *
     * * `null` | `StateFlowSlot` -- it is not used right now. Can [allocate] to new collector. Points to next free.
     * * `NONE` -- used by a collector, but neither suspended nor has pending value.
     * * `T` | `Closed` -- pending value or closed token. [NULL] is used for `null` values.
     * * `CancellableContinuationImpl<T>` -- suspended waiting for value.
     *
     * It is important that default `null` value is used, because there can be a race between allocation
     * of a new slot and trying to do [updateValue] on this slot.
     */
    private val _state = atomic<Any?>(null)
    private var fresh = false // true when this slot is fresh -- was allocated while update was in process
    
    // makes this slot allocated, returns a reference to the next free slot
    fun allocate(fresh: Boolean, value: Any): StateFlowSlot? {
        this.fresh = fresh // write fresh before volatile write to state
        val old = _state.getAndSet(value)
        return old as StateFlowSlot?
    }

    fun free(nextFree: StateFlowSlot?) {
        _state.value = nextFree
    }

    @Suppress("UNCHECKED_CAST")
    fun updateValue(value: Any, updateFresh: Boolean, updateStale: Boolean): Unit =
        _state.loop { state ->
            if (state == null || state is StateFlowSlot) return // this slot is free - skit it
            val wasFresh = fresh // read after volatile read of state
            // if we see non-null (allocated) state, then wasFresh correctly reflects what's going on
            val update = if (wasFresh) updateFresh else updateStale
            if (!update) return // do not update this slot
            if (state is CancellableContinuationImpl<*>) {
                // this slot is suspended -- resume it
                if (_state.compareAndSet(state, NONE)) {
                    fresh = false // not fresh anymore
                    (state as CancellableContinuationImpl<Any?>).resume(value)
                    return
                }
            } else if (_state.compareAndSet(state, value)) {
                // this slot contains previous value (or NONE) -- save new value
                fresh = false // not fresh anymore
                return
            }
        }

    fun takeValue(): Any = _state.getAndSet(NONE)!!.also { state ->
        assert { state !is CancellableContinuationImpl<*> }
    }

    @Suppress("UNCHECKED_CAST")
    suspend fun takeValueSuspend(): Any = suspendCancellableCoroutine sc@ { cont ->
        val value = _state.getAndUpdate { state ->
            assert { state !is CancellableContinuationImpl<*> }
            if (state === NONE) cont else NONE
        }
        if (value !== NONE) {
            // there was a value -- resume now
            cont.resume(value!!)
        }
        // Note: we don't need cont.invokeOnCancellation. free will be called on cancellation anyway
    }
}

private class StateFlowImpl<T>(initialValue: Any) : SynchronizedObject(), MutableStateFlow<T>, FusibleFlow<T> {
    private val _value = atomic(initialValue) // NONE | T!! | NULL | Closed
    private var sequence = 0 // serializes updates, value update is in process when sequence is odd
    private var hasFresh = false // true when we have freshly allocated slots during update
    private var slots = arrayOfNulls<StateFlowSlot?>(INITIAL_SIZE)
    private var nextSlotIndex = 0 // total number of created StateFlowSlot objects in slots array
    private var firstFreeSlot: StateFlowSlot? = null // first free slot, forms a stack of created slots that are free

    public override val isInitialized: Boolean
        get() = _value.value !== NONE

    override val isClosed: Boolean
        get() = _value.value is Closed

    @Suppress("UNCHECKED_CAST")
    public override var value: T
        get() {
            val value = _value.value
            check(value !== NONE) { "StateFlow is not initialized" }
            check(value !is Closed) { "StateFlow is closed" }
            return NULL.unbox(value)
        }
        set(value) {
            require(value !is CancellableContinuationImpl<*>) // just in case
            check(update(value ?: NULL)) { "StateFlow is closed" }
        }

    // Update returns false when the data flow was already closed
    private fun update(value: Any): Boolean {
        var curSequence = 0
        var curSlots: Array<StateFlowSlot?> = this.slots // benign race, we will not use it
        var curValue = value
        var updateFresh = false
        var updateStale = true  // update all stale values on first pass
        synchronized(this) {
            val oldValue = _value.value
            if (oldValue is Closed) return false // already closed 
            if (oldValue == value) return true // Don't do anything if value is not changing
            _value.value = value
            curSequence = sequence
            if (curSequence and 1 == 0) { // even value, quiescent state
                curSequence++ // make it odd
                sequence = curSequence
            } else {
                // update is already in process, notify it, and return
                sequence = curSequence + 2 // change sequence to notify, keep it odd
                return true
            }
            curSlots = slots // read current reference to collectors under lock
        }
        // Fire value updates outside of the lock to avoid deadlocks with unconfined coroutines
        // Loop until we're done firing all the changes (this is sort of simple flat combining)
        while (true) {
            // Benign race on element read from array
            for (col in curSlots) {
                col?.updateValue(curValue, updateFresh, updateStale)
            }
            // check if the value was updated again while we were updating the old one
            synchronized(this) {
                updateFresh = hasFresh // see if we need a loop to update fresh values
                updateStale = sequence != curSequence // see if we need a loop to update stale values again
                hasFresh = false // reset fresh flag for next update
                if (!updateFresh && !updateStale) { // nothing changed
                    sequence = curSequence + 1 // make sequence even again
                    return true // done
                }
                // reread everything for the next loop under the lock
                curSequence = sequence
                curSlots = slots
                curValue = _value.value
            }
        }
    }

    override fun close(cause: Throwable?): Boolean = update(Closed(cause))

    @Suppress("UNCHECKED_CAST")
    override suspend fun collect(collector: FlowCollector<T>) {
        val slot = allocateSlot()
        try {
            while (true) {
                var value = slot.takeValue()
                // Note: if takeValueSuspend is cancelled, then it bails out of this loop and calls freeSlot
                if (value === NONE) {
                    value = slot.takeValueSuspend()
                    assert { value !== NONE }
                }
                if (value is Closed) {
                    value.cause?.let { throw it }
                    break
                }
                collector.emit(NULL.unbox(value))
            }
        } finally {
            freeSlot(slot)
        }
    }

    private fun allocateSlot(): StateFlowSlot = synchronized(this) {
        // If we have a free slot in the freeS -- restore it, otherwise create new
        val slot = firstFreeSlot ?: run {
            val size = slots.size
            if (nextSlotIndex >= size) slots = slots.copyOf(2 * size)
            StateFlowSlot(nextSlotIndex++)
        }
        // We allocate slot with existing value only when the value is not currently being updated.
        // Otherwise update may or may not see the newly allocated slot, so we mark it as "fresh"
        // and let update loop again and deliver the value to the fresh slots exactly once.
        val fresh = sequence and 1 != 0
        val value = if (fresh) NONE else _value.value
        if (fresh) hasFresh = true // force update to loop again
        firstFreeSlot = slot.allocate(fresh, value)
        slots[slot.index] = slot // write this slot to its index in array
        slot
    }

    private fun freeSlot(slot: StateFlowSlot): Unit = synchronized(this) {
        slot.free(firstFreeSlot)
        firstFreeSlot = slot
        slots[slot.index] = null // clear index in array to speed up update (it does not have to look inside free slots)
    }

    override fun fuse(context: CoroutineContext, capacity: Int): FusibleFlow<T> {
        // context is irrelevant for data flow and it is always conflated
        // so it should not do anything unless buffering is requested
        return when (capacity) {
            Channel.CONFLATED, Channel.RENDEZVOUS -> this
            else -> ChannelFlowOperatorImpl(this, context, capacity)
        }
    }

    private class Closed(@JvmField val cause: Throwable?)
}
