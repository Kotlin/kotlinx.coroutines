package kotlinx.coroutines.flow

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

internal abstract class AbstractHotFlowSlot<F> {
    abstract fun allocateLocked(flow: F): Boolean
    abstract fun freeLocked(flow: F): List<Continuation<Unit>>? // returns a list of continuation to resume after lock
}

internal abstract class AbstractHotFlow<S : AbstractHotFlowSlot<*>> : SynchronizedObject() {
    @Suppress("UNCHECKED_CAST")
    protected var slots: Array<S?>? = null // allocated when needed
        private set
    protected var nCollectors = 0 // number of allocated (!free) slots
        private set
    private var nextIndex = 0 // oracle for the next free slot index
    private var _numberOfCollectors: MutableStateFlow<Int>? = null // init on first need

    val numberOfCollectors: StateFlow<Int>
        get() = synchronized(this) {
            _numberOfCollectors ?: MutableStateFlow(nCollectors).also {
                _numberOfCollectors = it
            }
        }

    protected abstract fun createSlot(): S

    protected abstract fun createSlotArray(size: Int): Array<S?>

    @Suppress("UNCHECKED_CAST")
    protected fun allocateSlot(): S {
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
                if ((slot as AbstractHotFlowSlot<Any>).allocateLocked(this)) break // break when found and allocated free slot
            }
            nextIndex = index
            nCollectors++
            slot
        }
        // todo: update _numberOfCollectors
        return slot
    }

    @Suppress("UNCHECKED_CAST")
    protected fun freeSlot(slot: S): Unit {
        val resumeList = synchronized(this) {
            nCollectors--
            (slot as AbstractHotFlowSlot<Any>).freeLocked(this)
        }
        // todo: update _numberOfCollectors
        resumeList?.forEach { it.resume(Unit) }
    }
}