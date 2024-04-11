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
     * The default value of 0 means that either the node is not in any list or [LockFreeLinkedListHead.addLast] wasn't
     * yet called on it.
     */
    var address: Long = 0
}

/** @suppress **This is unstable API and it is subject to change.** */
internal open class LockFreeLinkedListHead: LockFreeLinkedListSegment(
    id = 0,
    prev = null,
    pointers = 2,
) {
    private val tail = atomic<LockFreeLinkedListSegment>(this)
    private val nextElement = atomic(0L)

    /**
     * The list of bits that are forbidden from entering the list.
     *
     * TODO: we can store this in `cleanedAndPointers`, there's enough space for that there.
     */
    private val forbiddenBits: AtomicInt = atomic(0)

    /**
     * Iterates over all non-removed elements in this list, skipping every node until (and including) [startAfter].
     */
    inline fun forEach(
        forbidBitmask: Byte = 0,
        startInSegment: LockFreeLinkedListSegment? = null,
        startAfterIndex: Int? = null,
        block: (LockFreeLinkedListNode, LockFreeLinkedListSegment, Int) -> Unit
    ) {
        forbiddenBits.update { it or forbidBitmask.toInt() }
        var segment: LockFreeLinkedListSegment? = startInSegment ?: this
        var startIndex: Int = startAfterIndex?.let { it + 1 } ?: 0
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
        node.address = addLastWithoutModifying(node, permissionsBitmask) ?: return false
        return true
    }

    /**
     * Adds the [node] to the end of the list if every bit in [permissionsBitmask] is still allowed in the list.
     * As opposed to [addLast], doesn't modify the [node]'s address.
     */
    fun addLastWithoutModifying(node: LockFreeLinkedListNode, permissionsBitmask: Byte): Long? {
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
            index
        } else {
            null
        }
    }

    fun remove(node: LockFreeLinkedListNode) {
        val address = node.address
        val id = address / SEGMENT_SIZE
        var segment: LockFreeLinkedListSegment = this
        while (segment.id < id) { segment = segment.next!! }
        if (segment.id == id) {
            segment.clearSlot((address % SEGMENT_SIZE).toInt(), node)
        }
    }
}

internal open class LockFreeLinkedListSegment(
    id: Long,
    prev: LockFreeLinkedListSegment?,
    pointers: Int,
) : Segment<LockFreeLinkedListSegment>(id = id, prev = prev, pointers = pointers)
{
    /** Each cell is a [LockFreeLinkedListNode], a [BrokenForSomeElements], or `null`. */
    private val cells = atomicArrayOfNulls<Any>(SEGMENT_SIZE)

    override val numberOfSlots: Int get() = SEGMENT_SIZE

    fun clearSlot(index: Int, node: LockFreeLinkedListNode) {
        if (cells[index].compareAndSet(node, null))
            onSlotCleaned()
    }

    inline fun forEach(forbidBitmask: Byte, startIndex: Int, block: (LockFreeLinkedListNode, LockFreeLinkedListSegment, Int) -> Unit) {
        for (i in startIndex until SEGMENT_SIZE) {
            val node = breakCellOrGetValue(forbidBitmask, i)
            if (node != null) block(node, this, i)
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

private fun createSegment(id: Long, prev: LockFreeLinkedListSegment): LockFreeLinkedListSegment =
    LockFreeLinkedListSegment(
        id = id,
        prev = prev,
        pointers = 0,
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
