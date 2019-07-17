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

/**
 * A [Flow] that contains a single updatable data [value].
 *
 * A data flow can be created with `DataFlow()` constructor function either without an initial value
 * or with an initial value. Data value can be updated by setting its [value] property.
 * Updates to the [value] are always [conflated][Flow.conflate]. So a slow collector will skip fast updates,
 * but always collects the most recently emitted value.
 *
 * The name reflects the fact that [DataFlow] represents an cell in a "data flow programming" model
 * (think of an electronic spreadsheet). Dependent values can be defined by using various operators on the
 * flows, with [combineLatest] being especially useful to combine multiple data flows using arbitrary functions.
 *
 * A data flow can be [closed][close] and all its collectors will complete.
 *
 * A read-only interface to data flow is a [Flow]. It is supposed to be collected by the consumers of the data.
 * The ability to read the current [value] is provided only for convenience of the code that updates the data.
 * For example, the following class encapsulates an integer data flow and increments its value on each call to `inc`:
 *
 * ```
 * class CounterModel {
 *     private val _counter = DataFlow(0) // private data flow
 *     val counter: Flow<Int> get() = _counter // publicly exposed as a flow
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
 * val sum = aModel.counter.combineLatest(bModel.counter) { a, b -> a + b }
 * ```
 *
 * Conceptually data flow is similar to
 * [ConflatedBroadcastChannel][kotlinx.coroutines.channels.ConflatedBroadcastChannel]
 * but it is simpler, because it does not have to implement all the channel APIs.
 *
 * All methods of data flow are **thread-safe** and can be safely invoked from concurrent coroutines without
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
 * Data flow implementation is optimized for memory consumption and allocation-freedom. It uses a lock to ensure
 * thread-safety, but suspending collector coroutines are resumed outside of this lock to avoid dead-locks when
 * using unconfined coroutines. Adding new collectors has `O(1)` amortized code, but updating a [value] has `O(N)`
 * cost, where `N` is the number of collectors.
 */
@FlowPreview
public interface DataFlow<T> : Flow<T> {
    /**
     * Returns `true` if this data flow is initialized.
     *
     * A data flow is initialized when its [value] was set at least once.
     * A [closed][isClosed] data flow is considered to be initialized.
     */
    public val isInitialized: Boolean

    /**
     * Returns `true` if this data flow is closed.
     *
     * See [close].
     */
    public val isClosed: Boolean

    /**
     * Value of this data flow.
     *
     * Setting a value that is [equal][Any.equals] to the previous one does nothing. 
     *
     * Getting a value from an [uninitialized][isInitialized] flow produces [IllegalStateException].
     * Getting a value from or setting a value to a [closed][isClosed] flow produces [IllegalStateException].
     */
    public var value: T

    /**
     * Closes this data fl9w.
     * This is an idempotent operation -- subsequent invocations of this function have no effect and return `false`.
     * Conceptually, its sets a value to a special "close token" and all active and future collector from
     * this [Flow] complete either normally (when [cause] is null) or with the corresponding exception that
     * was specified as a [cause].
     */
    public fun close(cause: Throwable? = null): Boolean
}

/**
 * Creates an uninitialized [DataFlow].
 */
@Suppress("FunctionName")
@FlowPreview
public fun <T> DataFlow(): DataFlow<T> = DataFlowImpl(NONE)

/**
 * Creates a [DataFlow] with a given initial [value].
 *
 * This is a shorthand for `DataFlow().apply { this.value = value }`.
 */
@Suppress("FunctionName")
@FlowPreview
public fun <T> DataFlow(value: T): DataFlow<T> = DataFlowImpl(value ?: NULL)

@SharedImmutable
private val NONE = Symbol("NONE")

private const val INITIAL_SIZE = 2 // optimized for just a few collectors

// DataFlow slots are allocated for its collectors
private class DataFlowSlot {
    /**
     * Each slot can have one of the following states:
     *
     * * `null` -- it is not used right now. Can [allocate] to new collector.
     * * `NONE` -- used by a collector, but neither suspended nor has pending value.
     * * `T` | `Closed` -- pending value or closed token. [NULL] is used for `null` values.
     * * `CancellableContinuationImpl<T>` -- suspended waiting for value.
     *
     * It is important that default `null` value is used, because there can be a race between allocation
     * of a new slot and trying to do [updateValue] on this slot.
     */
    private val _state = atomic<Any?>(null)
    private var fresh = false // true when this slot is fresh -- was allocated while update was in process

    val isFree: Boolean
        get() = _state.value === null

    fun allocate(fresh: Boolean, value: Any) {
        this.fresh = fresh // write fresh before volatile write to state
        val old = _state.getAndSet(value)
        assert { old == null }
    }

    fun free() {
        _state.value = null
    }

    @Suppress("UNCHECKED_CAST")
    fun updateValue(value: Any, updateFresh: Boolean, updateStale: Boolean): Unit =
        _state.loop { state ->
            if (state == null) return // this slot is free - skit it
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

    fun takeValue(): Any = _state.getAndSet(NONE)!!.also {
        assert { it !is CancellableContinuationImpl<*> }
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

private class DataFlowImpl<T>(initialValue: Any) : SynchronizedObject(), DataFlow<T>, FusibleFlow<T> {
    private val _value = atomic(initialValue) // NONE | T!! | NULL | Closed
    private var sequence = 0 // serializes updates, value update is in process when sequence is odd
    private var hasFresh = false // true when we have freshly allocated slots during update
    private var slots = arrayOfNulls<DataFlowSlot?>(INITIAL_SIZE)
    private var nSlots = 0 // number of allocated (!free) slots
    private var nextIndex = 0 // oracle for the next free slot index

    public override val isInitialized: Boolean
        get() = _value.value != NONE

    override val isClosed: Boolean
        get() = _value.value is Closed

    @Suppress("UNCHECKED_CAST")
    public override var value: T
        get() {
            val value = _value.value
            check(value !== NONE) { "DataFlow is not initialized" }
            check(value !is Closed) { "DataFlow is closed" }
            return NULL.unbox(value)
        }
        set(value) {
            require(value !is CancellableContinuationImpl<*>) // just in case
            check(update(value ?: NULL)) { "DataFlow is closed" }
        }

    // Update returns false when the data flow was already closed
    private fun update(value: Any): Boolean {
        var curSequence = 0
        var curSlots: Array<DataFlowSlot?> = this.slots // benign race, we will not use it
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

    private fun allocateSlot(): DataFlowSlot = synchronized(this) {
        val size = slots.size
        if (nSlots >= size) slots = slots.copyOf(2 * size)
        var index = nextIndex
        var slot: DataFlowSlot
        while (true) {
            slot = slots[index] ?: DataFlowSlot().also { slots[index] = it }
            index++
            if (index >= slots.size) index = 0
            if (slot.isFree) break
        }
        // We allocate slot with existing value only when the value is not currently being updated.
        // Otherwise update may or may not see the newly allocated slot, so we mark it as "fresh"
        // and let update loop again and deliver the value to the fresh slots exactly once.
        val fresh = sequence and 1 != 0
        val value = if (fresh) NONE else _value.value
        if (fresh) hasFresh = true // force update to loop again
        slot.allocate(fresh, value)
        nextIndex = index
        nSlots++
        slot
    }

    private fun freeSlot(slot: DataFlowSlot): Unit = synchronized(this) {
        slot.free()
        nSlots--
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
