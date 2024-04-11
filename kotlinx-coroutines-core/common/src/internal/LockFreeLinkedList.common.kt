@file:Suppress("NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.experimental.*
import kotlin.jvm.*

/** @suppress **This is unstable API and it is subject to change.** */
internal open class LockFreeLinkedListNode {
    /**
     * Try putting this node into a list.
     *
     * Returns:
     * - The new head of the list if the operation succeeded.
     * - The head of the list if someone else concurrently added this node to the list,
     *   but no other modifications to the list were made.
     */
    fun attachToList(head: LockFreeLinkedListHead): LockFreeLinkedListHead {
        val newAddress = head.addLastWithoutModifying(this, permissionsBitmask = 0)
        assert { newAddress != null }
        return if (_address.compareAndSet(null, newAddress)) {
            head
        } else {
            _address.value!!.segment.head
        }
    }

    /**
     * Remove this node from the list.
     */
    open fun remove() {
        _address.value?.let {
            val segment = it.segment
            segment.clearSlot(it.index)
        }
    }

    private val _address = atomic<Address?>(null)

    val address: Address get() = _address.value!!

    internal fun trySetAddress(address: Address) = this._address.compareAndSet(null, address)
}

/** @suppress **This is unstable API and it is subject to change.** */
internal open class LockFreeLinkedListHead {
    private val head = LockFreeLinkedListSegment(
        id = 0,
        prev = null,
        pointers = 2,
        head = this,
    )
    private val tail = atomic(head)
    private val nextElement = atomic(0L)

    /**
     * The list of bits that are forbidden from entering the list.
     *
     * TODO: we can store this in the extra bits in [head], there's enough space for that there, and it's never removed.
     */
    private val forbiddenBits: AtomicInt = atomic(0)

    /**
     * Iterates over all non-removed elements in this list, skipping every node until (and including) [startAfter].
     */
    inline fun forEach(
        forbidBitmask: Byte = 0,
        startAfter: LockFreeLinkedListNode? = null,
        block: (LockFreeLinkedListNode) -> Unit
    ) {
        forbiddenBits.update { it or forbidBitmask.toInt() }
        val startAddress = startAfter?.address
        var segment: LockFreeLinkedListSegment? = startAddress?.segment ?: head
        var startIndex: Int = startAddress?.index?.let { it + 1 } ?: 0
        while (segment != null) {
            segment.forEach(forbidBitmask = forbidBitmask, startIndex = startIndex, block = block)
            segment = segment.next
            startIndex = 0
        }
    }

    /**
     * Adds the [node] to the end of the list if every bit in [permissionsBitmask] is still allowed in the list,
     * and then sets the [node]'s address to the new address.
     */
    fun addLast(node: LockFreeLinkedListNode, permissionsBitmask: Byte): Boolean {
        val address = addLastWithoutModifying(node, permissionsBitmask) ?: return false
        val success = node.trySetAddress(address)
        assert { success }
        return true
    }

    /**
     * Adds the [node] to the end of the list if every bit in [permissionsBitmask] is still allowed in the list.
     * As opposed to [addLast], doesn't modify the [node]'s address.
     */
    fun addLastWithoutModifying(node: LockFreeLinkedListNode, permissionsBitmask: Byte): Address? {
        /** First, avoid modifying the list at all if it was already closed for elements like ours. */
        if (permissionsBitmask and forbiddenBits.value.toByte() != 0.toByte()) return null
        /** Obtain the place from which the desired segment will certainly be reachable. */
        val curTail = tail.value
        /** Allocate a place for our element. */
        val index = nextElement.getAndIncrement()
        /** Find or create a segment where the node can be stored. */
        val createNewSegment = ::createSegment // can't just pass the function, as the compiler crashes (KT-67332)
        val segmentId = index / SEGMENT_SIZE
        val segment = tail.findSegmentAndMoveForward(id = segmentId, curTail, createNewSegment).segment
        assert { segment.id == segmentId }
        val indexInSegment = (index % SEGMENT_SIZE).toInt()
        /** Double-check that it's still not forbidden for the node to enter the list. */
        if (permissionsBitmask and forbiddenBits.value.toByte() != 0.toByte()) return null
        /** Now we know that the list was still not closed at some point *even after the segment* was created.
         * Because [forbiddenBits] is set before [forEach] traverses the list, this means that [forEach] is guaranteed
         * to observe the new segment and either break the cell where [node] wants to arrive or process the [node].
         * In any case, we have linearizable behavior. */
        return if (segment.tryAdd(node, permissionsBitmask = permissionsBitmask, indexInSegment = indexInSegment)) {
            Address(segment, indexInSegment)
        } else {
            null
        }
    }
}

internal open class LockFreeLinkedListSegment(
    id: Long,
    prev: LockFreeLinkedListSegment?,
    pointers: Int,
    /** Used only during promoting of a single node to a list to ensure wait-freedom of the promotion operation.
     * Without this, promotion can't be implemented without a (possibly bounded) spin loop: once the node is committed
     * to be part of some list, the other threads can't do anything until that one thread sets the state to be the
     * head of the list. */
    @JvmField val head: LockFreeLinkedListHead,
) : Segment<LockFreeLinkedListSegment>(id = id, prev = prev, pointers = pointers)
{
    /** Each cell is a [LockFreeLinkedListNode], a [BrokenForSomeElements], or `null`. */
    private val cells = atomicArrayOfNulls<Any>(SEGMENT_SIZE)

    override val numberOfSlots: Int get() = SEGMENT_SIZE

    fun clearSlot(index: Int) {
        cells[index].value = null
        onSlotCleaned()
    }

    inline fun forEach(forbidBitmask: Byte, startIndex: Int, block: (LockFreeLinkedListNode) -> Unit) {
        for (i in startIndex until SEGMENT_SIZE) {
            val node = breakCellOrGetValue(forbidBitmask, i)
            if (node != null) block(node)
        }
    }
    
    private fun breakCellOrGetValue(forbidBitmask: Byte, index: Int): LockFreeLinkedListNode? {
        while (true) {
            val value = cells[index].value
            if (value is BrokenForSomeElements?) {
                val newForbiddenBits = value.forbiddenBits or forbidBitmask
                if (newForbiddenBits == value.forbiddenBits
                    || cells[index].compareAndSet(value, BrokenForSomeElements.fromBitmask(newForbiddenBits)))
                    return null
            } else {
                return value as LockFreeLinkedListNode
            }
        }
    }

    /**
     * Adds the [node] to the array of cells if the slot wasn't broken.
     */
    fun tryAdd(node: LockFreeLinkedListNode, permissionsBitmask: Byte, indexInSegment: Int): Boolean {
        if (cells[indexInSegment].compareAndSet(null, node)) return true
        cells[indexInSegment].loop { value ->
            // This means that some elements are forbidden from entering the list.
            value as BrokenForSomeElements
            // Are *we* forbidden from entering the list?
            if (value.forbiddenBits and permissionsBitmask != 0.toByte()) {
                cells[indexInSegment].value = BrokenForSomeElements.FULLY_BROKEN
                onSlotCleaned()
                return false
            }
            // We aren't forbidden. Let's try entering it.
            if (cells[indexInSegment].compareAndSet(value, node)) return true
        }
    }

    override fun onCancellation(index: Int, cause: Throwable?, context: CoroutineContext) {
        throw UnsupportedOperationException("Cancellation is not supported on LockFreeLinkedList")
    }
}

internal class Address(@JvmField val segment: LockFreeLinkedListSegment, @JvmField val index: Int)

private fun createSegment(id: Long, prev: LockFreeLinkedListSegment): LockFreeLinkedListSegment =
    LockFreeLinkedListSegment(
        id = id,
        prev = prev,
        pointers = 0,
        head = prev.head
    )

private const val SEGMENT_SIZE = 8

@JvmInline
private value class BrokenForSomeElements private constructor(val forbiddenBits: Byte) {
    companion object {
        fun fromBitmask(forbiddenBits: Byte): BrokenForSomeElements? = when (forbiddenBits) {
            0.toByte() -> null // no one is forbidden
            else -> BrokenForSomeElements(forbiddenBits)
        }

        val FULLY_BROKEN = BrokenForSomeElements(255.toByte())
    }
}

private val BrokenForSomeElements?.forbiddenBits get() = this?.forbiddenBits ?: 0
