/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.assert
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

internal abstract class AbstractSharedFlowSlot<F> {
    abstract fun allocateLocked(flow: F): Boolean
    abstract fun freeLocked(flow: F): List<Continuation<Unit>>? // returns a list of continuation to resume after lock
}

internal abstract class AbstractSharedFlow<S : AbstractSharedFlowSlot<*>> : SynchronizedObject() {
    @Suppress("UNCHECKED_CAST")
    protected var slots: Array<S?>? = null // allocated when needed
        private set
    protected var nCollectors = 0 // number of allocated (!free) slots
        private set
    private var nextIndex = 0 // oracle for the next free slot index
    private var _subscriptionCount: MutableStateFlow<Int>? = null // init on first need

    val subscriptionCount: StateFlow<Int>
        get() = synchronized(this) {
            // allocate under lock in sync with nCollectors variable
            _subscriptionCount ?: MutableStateFlow(nCollectors).also {
                _subscriptionCount = it
            }
        }

    protected abstract fun createSlot(): S

    protected abstract fun createSlotArray(size: Int): Array<S?>

    @Suppress("UNCHECKED_CAST")
    protected fun allocateSlot(): S {
        // Actually create slot under lock
        var subscriptionCount: MutableStateFlow<Int>? = null
        val slot = synchronized(this) {
            val slots = when(val curSlots = slots) {
                null -> createSlotArray(2).also { slots = it }
                else -> if (nCollectors >= curSlots.size) {
                    curSlots.copyOf(2 * curSlots.size).also { slots = it }
                } else {
                    curSlots
                }
            }
            var index = nextIndex
            var slot: S
            while (true) {
                slot = slots[index] ?: createSlot().also { slots[index] = it }
                index++
                if (index >= slots.size) index = 0
                if ((slot as AbstractSharedFlowSlot<Any>).allocateLocked(this)) break // break when found and allocated free slot
            }
            nextIndex = index
            nCollectors++
            subscriptionCount = _subscriptionCount // retrieve under lock if initialized
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
        val resumeList = synchronized(this) {
            nCollectors--
            subscriptionCount = _subscriptionCount // retrieve under lock if initialized
            // Reset next index oracle if we have no more active collectors for more predictable behavior next time
            if (nCollectors == 0) nextIndex = 0
            (slot as AbstractSharedFlowSlot<Any>).freeLocked(this)
        }
        // Resume suspended coroutines
        resumeList?.forEach { it.resume(Unit) }
        // decrement subscription count
        subscriptionCount?.increment(-1)
    }

    protected inline fun forEachSlotLocked(block: (S) -> Unit) {
        if (nCollectors == 0) return
        slots?.forEach { slot ->
            if (slot != null) block(slot)
        }
    }
}