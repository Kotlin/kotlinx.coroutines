package kotlinx.coroutines.internal

import kotlinx.atomicfu.atomic

/**
 * This queue implementation is based on [SegmentQueue] for testing purposes and is organized as follows. Essentially,
 * the [SegmentBasedQueue] is represented as an infinite array of segments, each stores one element (see [OneElementSegment]).
 * Both [enqueue] and [dequeue] operations increment the corresponding global index ([enqIdx] for [enqueue] and
 * [deqIdx] for [dequeue]) and work with the indexed by this counter cell. Since both operations increment the indices
 * at first, there could be a race: [enqueue] increments [enqIdx], then [dequeue] checks that the queue is not empty
 * (that's true) and increments [deqIdx], looking into the corresponding cell after that; however, the cell is empty
 * because the [enqIdx] operation has not been put its element yet. To make the queue non-blocking, [dequeue] can mark
 * the cell with [BROKEN] token and retry the operation, [enqueue] at the same time should restart as well; this way,
 * the queue is obstruction-free.
 */
internal class SegmentBasedQueue<T> : SegmentQueue<OneElementSegment<T>>() {
    override fun newSegment(id: Long, prev: OneElementSegment<T>?): OneElementSegment<T> = OneElementSegment(id, prev)

    private val enqIdx = atomic(0L)
    private val deqIdx = atomic(0L)

    // Returns the segments associated with the enqueued element.
    fun enqueue(element: T): OneElementSegment<T> {
        while (true) {
            var tail = this.tail
            val enqIdx = this.enqIdx.getAndIncrement()
            tail = getSegment(tail, enqIdx) ?: continue
            if (tail.element.value === BROKEN) continue
            if (tail.element.compareAndSet(null, element)) return tail
        }
    }

    fun dequeue(): T? {
        while (true) {
            if (this.deqIdx.value >= this.enqIdx.value) return null
            var firstSegment = this.head
            val deqIdx = this.deqIdx.getAndIncrement()
            firstSegment = getSegmentAndMoveHead(firstSegment, deqIdx) ?: continue
            var el = firstSegment.element.value
            if (el === null) {
                if (firstSegment.element.compareAndSet(null, BROKEN)) continue
                else el = firstSegment.element.value
            }
            if (el === REMOVED) continue
            return el as T
        }
    }

    val numberOfSegments: Int get() {
        var s: OneElementSegment<T>? = head
        var i = 0
        while (s != null) {
            s = s.next
            i++
        }
        return i
    }
}

internal class OneElementSegment<T>(id: Long, prev: OneElementSegment<T>?) : Segment<OneElementSegment<T>>(id, prev) {
    val element = atomic<Any?>(null)

    override val removed get() = element.value === REMOVED

    fun removeSegment() {
        element.value = REMOVED
        remove()
    }
}

private val BROKEN = Symbol("BROKEN")
private val REMOVED = Symbol("REMOVED")