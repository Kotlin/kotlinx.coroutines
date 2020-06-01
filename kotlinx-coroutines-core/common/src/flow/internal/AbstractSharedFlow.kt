/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.atomicfu.*
import kotlinx.atomicfu.locks.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*
import kotlin.jvm.*
import kotlin.native.concurrent.*

@JvmField
@SharedImmutable
internal val EMPTY_RESUMES = arrayOfNulls<Continuation<Unit>?>(0)

internal abstract class AbstractSharedFlowSlot<F> {
    abstract fun allocateLocked(flow: F): Boolean
    abstract fun freeLocked(flow: F): Array<Continuation<Unit>?> // returns continuations to resume after lock
}

internal class SharedFlowState<S>(
    val size: Int // size of array, see afu#149
) {
    private val arr: AtomicArray<S?> = atomicArrayOfNulls(size)

    operator fun set(index: Int, value: S?) {
        arr[index].value = value
    }

    operator fun get(index: Int): S? = arr[index].value

    fun getBufferAt(index: Long): Any? {
        return get(index.toInt() and (size - 1))
    }

    fun setBufferAt(index: Long, item: S) {
        arr.get(index.toInt() and (size - 1)).value = item
    }

    fun copyInto(newSlots: SharedFlowState<S>) {
        for (i in 0 until size) {
            newSlots.arr[i].value = get(i)
        }
    }
}

internal abstract class AbstractSharedFlow<S : AbstractSharedFlowSlot<*>> : SynchronizedObject() {
    private val _slots = atomic<SharedFlowState<S>?>(null) // allocated when needed
    protected val slots: SharedFlowState<S>? get() = _slots.value
    private val _nCollectors = atomic(0) // number of allocated (!free) slots
    protected val nCollectors: Int get()  = _nCollectors.value // number of allocated (!free) slots

    private val nextIndex = atomic(0) // oracle for the next free slot index
    private val _subscriptionCount = atomic<MutableStateFlow<Int>?>(null) // init on first need

    val subscriptionCount: StateFlow<Int>
        get() = synchronized(this) {
            // allocate under lock in sync with nCollectors variable
            _subscriptionCount.value ?: MutableStateFlow(nCollectors).also {
                _subscriptionCount.value = it
            }
        }

    protected abstract fun createSlot(): S

    @Suppress("UNCHECKED_CAST")
    protected fun allocateSlot(): S {
        // Actually create slot under lock
        var subscriptionCount: MutableStateFlow<Int>? = null
        val slot = synchronized(this) {
            val slots = when (val curSlots = _slots.value) {
                null -> SharedFlowState<S>(2).also { _slots.value = it }
                else -> if (nCollectors >= curSlots.size) {
                    val newSlots = SharedFlowState<S>(2 * curSlots.size)
                    curSlots.copyInto(newSlots)
                    _slots.value = newSlots
                    newSlots
                } else {
                    curSlots
                }
            }
            var index = nextIndex.value
            var slot: S
            while (true) {
                slot = slots[index] ?: createSlot().also { slots[index] = it }
                index++
                if (index >= slots.size) index = 0
                if ((slot as AbstractSharedFlowSlot<Any>).allocateLocked(this)) break // break when found and allocated free slot
            }
            nextIndex.value = index
            _nCollectors.incrementAndGet()
            subscriptionCount = _subscriptionCount.value // retrieve under lock if initialized
            slot
        }
        // increments subscription count
        subscriptionCount?.increment(1)
        return slot
    }

    @Suppress("UNCHECKED_CAST")
    protected fun freeSlot(slot: S) {
        // Release slot under lock
        var subscriptionCount: MutableStateFlow<Int>? = null
        val resumes = synchronized(this) {
            _nCollectors.decrementAndGet()
            subscriptionCount = _subscriptionCount.value // retrieve under lock if initialized
            // Reset next index oracle if we have no more active collectors for more predictable behavior next time
            if (_nCollectors.value == 0) nextIndex.value = 0
            (slot as AbstractSharedFlowSlot<Any>).freeLocked(this)
        }
        /*
           Resume suspended coroutines.
           This can happens when the subscriber that was freed was a slow one and was holding up buffer.
           When this subscriber was freed, previously queued emitted can now wake up and are resumed here.
        */
        for (cont in resumes) cont?.resume(Unit)
        // decrement subscription count
        subscriptionCount?.increment(-1)
    }

    protected inline fun forEachSlotLocked(block: (S) -> Unit) {
        if (_nCollectors.value == 0) return
        val _slots = _slots.value
        if (_slots != null) {
            for (i in 0 until _slots.size) {
                val slot = _slots.get(i)
                if (slot != null) block(slot)
            }
        }
    }
}
